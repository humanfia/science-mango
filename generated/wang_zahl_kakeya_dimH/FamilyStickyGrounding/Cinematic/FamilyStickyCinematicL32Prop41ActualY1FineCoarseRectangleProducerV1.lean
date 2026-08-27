import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32ActualProjectedCenteredHalfY1AutomaticPointSlopeV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41CoarseRectangleIncidenceDataV1

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000

open Set

namespace FamilyStickyCinematicL32Prop41ActualY1FineCoarseRectangleProducerV1

open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open FamilyStickyCinematicL32ActualProjectedCenteredHalfPointSourceV1
open FamilyStickyCinematicL32ActualProjectedCenteredHalfTangencyStageV1
open FamilyStickyCinematicL32ActualProjectedCenteredHalfY1ActiveGeometryV1
open FamilyStickyCinematicL32ActualProjectedCenteredHalfY1AutomaticPointSlopeV1
open FamilyStickyCinematicL32ActualProjectedY1PointCommonRectangleV1
open FamilyStickyCinematicL32CenteredFractionNestingV1
open FamilyStickyCinematicL32CurvilinearRectangleCarrierV1
open FamilyStickyCinematicL32CurvilinearRectanglePointMultiplicityV1
open FamilyStickyCinematicL32FiniteProjectedShadingMultiplicitySliceV1
open FamilyStickyCinematicL32Prop41CoarseRectangleIncidenceDataV1
open FamilyStickyCinematicL32RectangleTangencyV1
open FamilyStickyCinematicL32TubeC2GraphRectangleV1
open FamilyStickyCinematicL32Lemma57TubeTangencyDistanceV1
open FamilyStickyCinematicL32TubePairTraceV1
open FamilyStickyWZ2TubeCarrierCoordinateAdapterV1

noncomputable section

universe u v

/-!
# Actual `Y1` fine and coarse rectangle producer

For a point `q`, the paper's `R_q` is the graph strip of the selected
center curve `tubeAt q`, over the interval centered at `q.2` with the
prescribed square-root length.  The same construction at a larger vertical
and horizontal scale is the literal coarse rectangle assigned to `R_q`.

This module supplies those two `C2GraphRectangle`s and plugs them into
`CoarseRectangleIncidenceData`.  Point membership and fine-to-coarse carrier
containment are proved from the actual centered-tube point source and scalar
scale comparison.  No tangency or incomparability is stored in the data.

For an arbitrary active tube, the unconditional payload stops at its actual
point incidence and attained tangency bound.  The final theorem below proves
coarse graph tangency in the already-grounded coefficient-lower branch.  The
missing complementary step is precisely the full Lemma 3.8(2c) component
interior theorem; it is not represented as a field or an axiom here.
-/

/-- The actual graph rectangle of `T`, with base centered at `theta` and
length exactly `sqrt (delta / t)`. -/
def centeredTubeC2GraphRectangle
    {radius : NNReal} (T : Tube radius)
    (f f1 f2 : Real -> Real)
    (hf : forall z, HasDerivAt f (f1 z) z)
    (hf1 : forall z, HasDerivAt f1 (f2 z) z)
    (theta delta t : Real) : C2GraphRectangle :=
  tubeC2GraphRectangle T f f1 f2 hf hf1
    (theta - Real.sqrt (delta / t) / 2)
    (theta + Real.sqrt (delta / t) / 2)
    (by nlinarith [Real.sqrt_nonneg (delta / t)])

@[simp]
theorem centeredTubeC2GraphRectangle_length
    {radius : NNReal} (T : Tube radius)
    (f f1 f2 : Real -> Real)
    (hf : forall z, HasDerivAt f (f1 z) z)
    (hf1 : forall z, HasDerivAt f1 (f2 z) z)
    (theta delta t : Real) :
    (centeredTubeC2GraphRectangle T f f1 f2 hf hf1 theta delta t).rectangle.right -
        (centeredTubeC2GraphRectangle T f f1 f2 hf hf1 theta delta t).rectangle.left =
      Real.sqrt (delta / t) := by
  simp [centeredTubeC2GraphRectangle, tubeC2GraphRectangle]

@[simp]
theorem centeredTubeC2GraphRectangle_graph
    {radius : NNReal} (T : Tube radius)
    (f f1 f2 : Real -> Real)
    (hf : forall z, HasDerivAt f (f1 z) z)
    (hf1 : forall z, HasDerivAt f1 (f2 z) z)
    (theta delta t : Real) :
    (centeredTubeC2GraphRectangle T f f1 f2 hf hf1 theta delta t).rectangle.graph =
      cinematicTraceValue f (tubeGraphA T) (tubeGraphB T)
        (tubeGraphC T) (tubeGraphD T) := by
  rfl

/-- The center parameter always belongs to the literal centered base. -/
theorem center_mem_centeredTubeC2GraphRectangle_base
    {radius : NNReal} (T : Tube radius)
    (f f1 f2 : Real -> Real)
    (hf : forall z, HasDerivAt f (f1 z) z)
    (hf1 : forall z, HasDerivAt f1 (f2 z) z)
    (theta delta t : Real) :
    theta ∈
      (centeredTubeC2GraphRectangle T f f1 f2 hf hf1 theta delta t).rectangle.base := by
  change theta ∈ Icc
    (theta - Real.sqrt (delta / t) / 2)
    (theta + Real.sqrt (delta / t) / 2)
  constructor <;> nlinarith [Real.sqrt_nonneg (delta / t)]

/-- A literal point on the `delta`-thick selected tube graph lies in `R_q`.
This is the kernel-checked `x in R_x` part of the paper's construction. -/
theorem point_mem_centeredTubeC2GraphRectangle_carrier
    {radius : NNReal} (T : Tube radius)
    (f f1 f2 : Real -> Real)
    (hf : forall z, HasDerivAt f (f1 z) z)
    (hf1 : forall z, HasDerivAt f1 (f2 z) z)
    (q : Real × Real) (delta t : Real)
    (hpoint :
      |q.1 - cinematicTraceValue f (tubeGraphA T) (tubeGraphB T)
        (tubeGraphC T) (tubeGraphD T) q.2| <= delta) :
    q ∈ (centeredTubeC2GraphRectangle T f f1 f2 hf hf1 q.2 delta t).carrier
      delta := by
  exact ⟨center_mem_centeredTubeC2GraphRectangle_base
    T f f1 f2 hf hf1 q.2 delta t, by simpa using hpoint⟩

/-- Two centered rectangles on the same actual graph are nested whenever
both their vertical widths and their square-root base scales are nested. -/
theorem centeredTubeC2GraphRectangle_carrier_subset
    {radius : NNReal} (T : Tube radius)
    (f f1 f2 : Real -> Real)
    (hf : forall z, HasDerivAt f (f1 z) z)
    (hf1 : forall z, HasDerivAt f1 (f2 z) z)
    (theta fineDelta fineT coarseDelta coarseT : Real)
    (hdelta : fineDelta <= coarseDelta)
    (hscale : fineDelta / fineT <= coarseDelta / coarseT) :
    (centeredTubeC2GraphRectangle T f f1 f2 hf hf1 theta fineDelta fineT).carrier
        fineDelta ⊆
      (centeredTubeC2GraphRectangle T f f1 f2 hf hf1 theta coarseDelta coarseT).carrier
        coarseDelta := by
  have hsqrt : Real.sqrt (fineDelta / fineT) <=
      Real.sqrt (coarseDelta / coarseT) := Real.sqrt_le_sqrt hscale
  rintro q ⟨hqBase, hqVertical⟩
  refine ⟨?_, hqVertical.trans hdelta⟩
  change q.2 ∈ Icc
      (theta - Real.sqrt (coarseDelta / coarseT) / 2)
      (theta + Real.sqrt (coarseDelta / coarseT) / 2)
  change q.2 ∈ Icc
      (theta - Real.sqrt (fineDelta / fineT) / 2)
      (theta + Real.sqrt (fineDelta / fineT) / 2) at hqBase
  constructor <;> linarith [hqBase.1, hqBase.2]

/-- Honest finite fine/coarse rectangle data over any already-constructed
projected shading.  `fineRectangleAt` and `coarseRectangleAt` are not input
maps: both are computed from the actual selected tube graph at `pointAt r`. -/
noncomputable def y1FineCoarseRectangleData
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (fine : UniformTubeFamily radius iota)
    (Y1 : FiniteProjectedShading (Real × Real) iota)
    (fineLabels : Finset fineLabel) (pointAt : fineLabel -> Real × Real)
    (tubeAt : Real × Real -> Tube radius)
    (f f1 f2 : Real -> Real)
    (hf : forall z, HasDerivAt f (f1 z) z)
    (hf1 : forall z, HasDerivAt f1 (f2 z) z)
    (fineDelta fineT coarseDelta coarseT : Real) :
    CoarseRectangleIncidenceData (point := Real × Real)
      (radius := radius) (iota := iota) fineLabel where
  fine := fine
  shading := Y1
  fineLabels := fineLabels
  pointAt := pointAt
  fineRectangleAt := fun r =>
    centeredTubeC2GraphRectangle (tubeAt (pointAt r)) f f1 f2 hf hf1
      (pointAt r).2 fineDelta fineT
  coarseRectangleAt := fun r =>
    centeredTubeC2GraphRectangle (tubeAt (pointAt r)) f f1 f2 hf hf1
      (pointAt r).2 coarseDelta coarseT

/-- The specialization whose shading and selected center are the literal
centered-half `Y1` objects already produced in the repository. -/
noncomputable def actualCenteredHalfY1FineCoarseRectangleData
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (base : Set (Real × Real)) (hbase : MeasurableSet base)
    (fine : UniformTubeFamily radius iota)
    (physical : FiniteProjectedShading (Real × Real) iota)
    (fineLabels : Finset fineLabel) (pointAt : fineLabel -> Real × Real)
    (f f1 f2 : Real -> Real) (outerA outerB : Real)
    (hOuter : outerA <= outerB)
    (hf : forall z, HasDerivAt f (f1 z) z)
    (hf1 : forall z, HasDerivAt f1 (f2 z) z)
    (globalScale : Real) (globalCenter : Tube radius)
    (ceiling exponent threshold fineT coarseDelta coarseT : Real) :
    CoarseRectangleIncidenceData (point := Real × Real)
      (radius := radius) (iota := iota) fineLabel :=
  y1FineCoarseRectangleData fine
    (actualProjectedCenteredHalfTangencyY1 base hbase fine physical
      f f1 f2 outerA outerB hOuter hf hf1 globalScale globalCenter ceiling
      exponent threshold)
    fineLabels pointAt
    (actualProjectedCenteredHalfTangencyCenterTubeAt fine physical
      f f1 f2 outerA outerB hOuter hf hf1 globalScale globalCenter ceiling
      exponent)
    f f1 f2 hf hf1 (radius : Real) fineT coarseDelta coarseT

/-- A genuine good pair is exactly an actual `Y1` active incidence at the
fine label's source point (plus membership of that label). -/
theorem y1FineCoarseRectangleData_goodPair_iff
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (fine : UniformTubeFamily radius iota)
    (Y1 : FiniteProjectedShading (Real × Real) iota)
    (fineLabels : Finset fineLabel) (pointAt : fineLabel -> Real × Real)
    (tubeAt : Real × Real -> Tube radius)
    (f f1 f2 : Real -> Real)
    (hf : forall z, HasDerivAt f (f1 z) z)
    (hf1 : forall z, HasDerivAt f1 (f2 z) z)
    (fineDelta fineT coarseDelta coarseT : Real)
    (i : iota) (r : fineLabel) :
    (y1FineCoarseRectangleData fine Y1 fineLabels pointAt tubeAt
      f f1 f2 hf hf1 fineDelta fineT coarseDelta coarseT).GoodPair i r <->
      r ∈ fineLabels ∧ i ∈ Y1.activeAtPoint (pointAt r) := by
  rw [CoarseRectangleIncidenceData.GoodPair]
  simp only [y1FineCoarseRectangleData]
  constructor
  · rintro ⟨hiAmbient, hr, hiCarrier⟩
    exact ⟨hr, (Y1.mem_activeAtPoint (pointAt r) i).mpr
      ⟨hiAmbient, hiCarrier⟩⟩
  · rintro ⟨hr, hiActive⟩
    have hiData := (Y1.mem_activeAtPoint (pointAt r) i).mp hiActive
    exact ⟨hiData.1, hr, hiData.2⟩

/-- Filtering by `keep` never fabricates geometry: a retained pair still
gives a literal active `Y1` incidence. -/
theorem y1FineCoarseRectangleData_retainedPair_active
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (fine : UniformTubeFamily radius iota)
    (Y1 : FiniteProjectedShading (Real × Real) iota)
    (fineLabels : Finset fineLabel) (pointAt : fineLabel -> Real × Real)
    (tubeAt : Real × Real -> Tube radius)
    (f f1 f2 : Real -> Real)
    (hf : forall z, HasDerivAt f (f1 z) z)
    (hf1 : forall z, HasDerivAt f1 (f2 z) z)
    (fineDelta fineT coarseDelta coarseT : Real)
    (keep : iota -> fineLabel -> Prop) (i : iota) (r : fineLabel)
    (hpair : (i, r) ∈
      (y1FineCoarseRectangleData fine Y1 fineLabels pointAt tubeAt
        f f1 f2 hf hf1 fineDelta fineT coarseDelta coarseT).retainedGoodPairs
          keep) :
    r ∈ fineLabels ∧ i ∈ Y1.activeAtPoint (pointAt r) ∧ keep i r := by
  let D := y1FineCoarseRectangleData fine Y1 fineLabels pointAt tubeAt
    f f1 f2 hf hf1 fineDelta fineT coarseDelta coarseT
  have hretained := (D.mem_retainedGoodPairs_iff keep).mp hpair
  have hgood := (y1FineCoarseRectangleData_goodPair_iff fine Y1 fineLabels
    pointAt tubeAt f f1 f2 hf hf1 fineDelta fineT coarseDelta coarseT i r).mp
      hretained.1
  exact ⟨hgood.1, hgood.2, hretained.2⟩

/-- Fine rectangles produced at a point are literally contained in their
assigned coarse rectangles under the two scalar scale comparisons. -/
theorem y1FineCoarseRectangleData_fine_carrier_subset_coarse
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (fine : UniformTubeFamily radius iota)
    (Y1 : FiniteProjectedShading (Real × Real) iota)
    (fineLabels : Finset fineLabel) (pointAt : fineLabel -> Real × Real)
    (tubeAt : Real × Real -> Tube radius)
    (f f1 f2 : Real -> Real)
    (hf : forall z, HasDerivAt f (f1 z) z)
    (hf1 : forall z, HasDerivAt f1 (f2 z) z)
    (fineDelta fineT coarseDelta coarseT : Real)
    (hdelta : fineDelta <= coarseDelta)
    (hscale : fineDelta / fineT <= coarseDelta / coarseT)
    (r : fineLabel) :
    let D := y1FineCoarseRectangleData fine Y1 fineLabels pointAt tubeAt
      f f1 f2 hf hf1 fineDelta fineT coarseDelta coarseT
    (D.fineRectangleAt r).carrier fineDelta ⊆
      (D.coarseRectangleAt r).carrier coarseDelta := by
  dsimp only [y1FineCoarseRectangleData]
  exact centeredTubeC2GraphRectangle_carrier_subset
    (tubeAt (pointAt r)) f f1 f2 hf hf1 (pointAt r).2
      fineDelta fineT coarseDelta coarseT hdelta hscale

/-- The produced rectangle carrier is definitionally the vertical
neighborhood of the selected actual tube graph.  Thus the selected center
tube is tangent to its fine and coarse rectangles with factor exactly one;
this is a theorem, not stored incidence data. -/
theorem centeredTubeC2GraphRectangle_carrier_eq_tubeNeighborhood
    {radius : NNReal} (T : Tube radius)
    (f f1 f2 : Real -> Real)
    (hf : forall z, HasDerivAt f (f1 z) z)
    (hf1 : forall z, HasDerivAt f1 (f2 z) z)
    (theta delta t : Real) :
    (centeredTubeC2GraphRectangle T f f1 f2 hf hf1 theta delta t).carrier
        delta =
      cinematicVerticalNeighborhood
        (cinematicTraceValue f (tubeGraphA T) (tubeGraphB T)
          (tubeGraphC T) (tubeGraphD T))
        (centeredTubeC2GraphRectangle T f f1 f2 hf hf1
          theta delta t).rectangle.base delta := by
  rfl

/-- Strongest unconditional retained-incidence endpoint currently available.

The conclusion simultaneously gives the literal `Y1` activity, membership
of the source point in both `R_x` and its assigned coarse rectangle, actual
fine-to-coarse containment, the coefficient upper bound, and the attained
centered-half tangency bound.  It deliberately does not claim that the
whole rectangle lies in the active tube's graph neighborhood. -/
theorem retainedY1Pair_fine_coarse_membership_and_attainedTangency
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (fine : UniformTubeFamily radius iota)
    (physical : FiniteProjectedShading (Real × Real) iota)
    (E : Set (Real × Real))
    (Y1 : FiniteProjectedShading (Real × Real) iota)
    (fineLabels : Finset fineLabel) (pointAt : fineLabel -> Real × Real)
    (centerTube : Tube radius) (tubeAt : Real × Real -> Tube radius)
    (f f1 f2 : Real -> Real) (outerA outerB : Real)
    (hOuter : outerA <= outerB)
    (hf : forall z, HasDerivAt f (f1 z) z)
    (hf1 : forall z, HasDerivAt f1 (f2 z) z)
    (tGlobal globalDelta fineT : Real)
    (facts : ActualCenteredHalfY1ActiveGeometryFacts fine physical E
      Y1.activeAtPoint tubeAt f f1 f2 outerA outerB hOuter hf hf1
      tGlobal globalDelta)
    (pointSource : ActualCenteredHalfPointRectangleSource E centerTube tubeAt
      f outerA outerB tGlobal)
    (hpointE : forall r, r ∈ fineLabels -> pointAt r ∈ E)
    (hradiusDelta : (radius : Real) <= globalDelta)
    (hbaseScale : (radius : Real) / fineT <= globalDelta / tGlobal)
    (keep : iota -> fineLabel -> Prop) (i : iota) (r : fineLabel)
    (hpair : (i, r) ∈
      (y1FineCoarseRectangleData fine Y1 fineLabels pointAt tubeAt
        f f1 f2 hf hf1 (radius : Real) fineT globalDelta tGlobal).retainedGoodPairs
          keep) :
    let D := y1FineCoarseRectangleData fine Y1 fineLabels pointAt tubeAt
      f f1 f2 hf hf1 (radius : Real) fineT globalDelta tGlobal
    i ∈ Y1.activeAtPoint (pointAt r) ∧
      keep i r ∧
      pointAt r ∈ (D.fineRectangleAt r).carrier (radius : Real) ∧
      pointAt r ∈ (D.coarseRectangleAt r).carrier globalDelta ∧
      (D.fineRectangleAt r).carrier (radius : Real) ⊆
        (D.coarseRectangleAt r).carrier globalDelta ∧
      tubePairCoefficientDistance (fine.tubes i) (tubeAt (pointAt r)) <=
        6 * tGlobal ∧
      tubePairAttainedTangencyDistance (fine.tubes i) (tubeAt (pointAt r))
          f f1 f2
          (FamilyStickyCinematicL32CenteredFractionIntervalsV1.centeredFractionLeft
            outerA outerB (1 / 2 : Real))
          (FamilyStickyCinematicL32CenteredFractionIntervalsV1.centeredFractionRight
            outerA outerB (1 / 2 : Real))
          (centered_half_and_quarter_endpoints_ordered hOuter).1
          (fun z _hz => hf z) (fun z _hz => hf1 z) + (radius : Real) <=
        2 * globalDelta := by
  dsimp only
  let D := y1FineCoarseRectangleData fine Y1 fineLabels pointAt tubeAt
    f f1 f2 hf hf1 (radius : Real) fineT globalDelta tGlobal
  have hretained := y1FineCoarseRectangleData_retainedPair_active
    fine Y1 fineLabels pointAt tubeAt f f1 f2 hf hf1
      (radius : Real) fineT globalDelta tGlobal keep i r hpair
  have hqE : pointAt r ∈ E := hpointE r hretained.1
  have hfineMem : pointAt r ∈
      (D.fineRectangleAt r).carrier (radius : Real) := by
    dsimp only [D, y1FineCoarseRectangleData]
    exact point_mem_centeredTubeC2GraphRectangle_carrier
      (tubeAt (pointAt r)) f f1 f2 hf hf1 (pointAt r)
        (radius : Real) fineT (pointSource.hpointTube (pointAt r) hqE)
  have hcoarseMem : pointAt r ∈
      (D.coarseRectangleAt r).carrier globalDelta := by
    dsimp only [D, y1FineCoarseRectangleData]
    apply point_mem_centeredTubeC2GraphRectangle_carrier
    exact (pointSource.hpointTube (pointAt r) hqE).trans hradiusDelta
  have hcontain : (D.fineRectangleAt r).carrier (radius : Real) ⊆
      (D.coarseRectangleAt r).carrier globalDelta := by
    exact y1FineCoarseRectangleData_fine_carrier_subset_coarse
      fine Y1 fineLabels pointAt tubeAt f f1 f2 hf hf1
        (radius : Real) fineT globalDelta tGlobal hradiusDelta hbaseScale r
  exact ⟨hretained.2.1, hretained.2.2, hfineMem, hcoarseMem, hcontain,
    facts.hactiveCoefficientUpper (pointAt r) hqE i hretained.2.1,
    facts.hactiveTangencyUpper (pointAt r) hqE i hretained.2.1⟩

/-- A proved common strip converts the selected-center rectangle into an
explicit graph-neighborhood tangency statement for the other actual tube.
The only extra equalities identify the common strip's base with the canonical
base centered at the physical point. -/
theorem centeredTubeRectangle_tangent_to_other_of_commonStrip
    {radius : NNReal} (T U : Tube radius)
    (f f1 f2 : Real -> Real)
    (hf : forall z, HasDerivAt f (f1 z) z)
    (hf1 : forall z, HasDerivAt f1 (f2 z) z)
    {A B delta t budgetFactor cError theta : Real}
    (C : ActualPairLocalCanonicalQuarterCommonRectangle
      T U f A B delta t budgetFactor cError)
    (hx : C.x = theta - Real.sqrt (delta / t) / 2)
    (hy : C.y = theta + Real.sqrt (delta / t) / 2) :
    (centeredTubeC2GraphRectangle U f f1 f2 hf hf1 theta delta t).carrier
        delta ⊆
      cinematicVerticalNeighborhood
        (cinematicTraceValue f (tubeGraphA T) (tubeGraphB T)
          (tubeGraphC T) (tubeGraphD T))
        (centeredTubeC2GraphRectangle U f f1 f2 hf hf1
          theta delta t).rectangle.base
        (delta + 2 * C.graphRadius) := by
  let graphT : Real -> Real := cinematicTraceValue f
    (tubeGraphA T) (tubeGraphB T) (tubeGraphC T) (tubeGraphD T)
  let graphU : Real -> Real := cinematicTraceValue f
    (tubeGraphA U) (tubeGraphB U) (tubeGraphC U) (tubeGraphD U)
  have hgap : forall z, z ∈ Icc C.x C.y ->
      |graphT z - graphU z| <= 2 * C.graphRadius := by
    exact common_strip_tangency_forces_value_sublevel
      C.reference graphT graphU (Icc C.x C.y) C.hbaseRadius
      (by simpa only [graphT] using C.hfirst)
      (by simpa only [graphU] using C.hsecond)
  rintro q ⟨hqBase, hqVertical⟩
  refine ⟨hqBase, ?_⟩
  have hqCommonBase : q.2 ∈ Icc C.x C.y := by
    rw [hx, hy]
    exact hqBase
  have hgraphGap := hgap q.2 hqCommonBase
  calc
    |q.1 - graphT q.2| =
        |(q.1 - graphU q.2) + (graphU q.2 - graphT q.2)| := by
          ring_nf
    _ <= |q.1 - graphU q.2| + |graphU q.2 - graphT q.2| :=
      abs_add_le _ _
    _ = |q.1 - graphU q.2| + |graphT q.2 - graphU q.2| := by
      rw [abs_sub_comm (graphU q.2)]
    _ <= delta + 2 * C.graphRadius := by
      apply add_le_add
      · change |q.1 - cinematicTraceValue f
          (tubeGraphA U) (tubeGraphB U) (tubeGraphC U) (tubeGraphD U) q.2| <=
            delta at hqVertical
        simpa only [graphU] using hqVertical
      · exact hgraphGap

/-- In the grounded coefficient-lower branch, an actual active Y1 tube is
tangent to the literal coarse rectangle centered on tubeAt q.  The output
radius is explicit and its full budget is inherited from the constructed
common strip.  No rectangle tangency premise is assumed. -/
theorem activeY1_coarseRectangle_tangent_of_coefficientLower
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    (fine : UniformTubeFamily radius iota)
    (physical : FiniteProjectedShading (Real × Real) iota)
    (E : Set (Real × Real))
    (activeAtPoint : Real × Real -> Finset iota)
    (centerTube : Tube radius) (tubeAt : Real × Real -> Tube radius)
    (f f1 f2 : Real -> Real) (outerA outerB : Real)
    (hOuter : outerA <= outerB)
    (hf : forall z, HasDerivAt f (f1 z) z)
    (hf1 : forall z, HasDerivAt f1 (f2 z) z)
    (tGlobal globalDelta : Real)
    (facts : ActualCenteredHalfY1ActiveGeometryFacts fine physical E
      activeAtPoint tubeAt f f1 f2 outerA outerB hOuter hf hf1
      tGlobal globalDelta)
    (pointSource : ActualCenteredHalfPointRectangleSource E centerTube tubeAt
      f outerA outerB tGlobal)
    {budgetFactor stripRadius : Real}
    (hwidth : (1 / 2 : Real) <= outerB - outerA)
    (hglobalDelta : 0 < globalDelta) (htGlobal : 0 < tGlobal)
    (hsmallScale :
      2 * globalDelta - (radius : Real) < tGlobal / 2400)
    (hcanonicalMargin :
      Real.sqrt (globalDelta / tGlobal) / 2 <=
        3 * (outerB - outerA) / 32)
    (hparameter : forall z, z ∈ Icc outerA outerB -> |z| <= 1)
    (hft : forall z, z ∈ Icc outerA outerB -> |f z| <= 2)
    (hf1Lower : forall z, z ∈ Icc outerA outerB -> 1 <= |f1 z|)
    (hf1Upper : forall z, z ∈ Icc outerA outerB -> |f1 z| <= 2)
    (hf2 : forall z, z ∈ Icc outerA outerB -> |f2 z| <= 1 / 100)
    (hf2Continuous : ContinuousOn f2 (Icc outerA outerB))
    (hstripRadius : 0 < stripRadius)
    (q : Real × Real) (hq : q ∈ E)
    (i : iota) (hi : i ∈ activeAtPoint q)
    (hcoefficientLower :
      tGlobal / 2 <=
        tubePairCoefficientDistance (fine.tubes i) (tubeAt q))
    (hbudget :
      2 * stripRadius +
          (2 * (radius : Real) +
            (activeY1PointSlopeMargin (radius : Real) globalDelta tGlobal +
                30 * tGlobal *
                  (Real.sqrt (globalDelta / tGlobal) / 2)) *
              (Real.sqrt (globalDelta / tGlobal) / 2)) +
            (radius : Real) / 2 <=
        budgetFactor * globalDelta) :
    let R := centeredTubeC2GraphRectangle (tubeAt q) f f1 f2 hf hf1
      q.2 globalDelta tGlobal
    exists graphRadius,
      R.carrier globalDelta ⊆
        cinematicVerticalNeighborhood
          (cinematicTraceValue f
            (tubeGraphA (fine.tubes i)) (tubeGraphB (fine.tubes i))
            (tubeGraphC (fine.tubes i)) (tubeGraphD (fine.tubes i)))
          R.rectangle.base (globalDelta + 2 * graphRadius) ∧
      2 * graphRadius + (radius : Real) / 2 <=
        budgetFactor * globalDelta := by
  dsimp only
  let C :=
    activeY1_point_to_localCanonicalQuarterCommonRectangle_of_coefficientLower
      fine physical E activeAtPoint centerTube tubeAt f f1 f2 outerA outerB
      hOuter hf hf1 tGlobal globalDelta facts pointSource hwidth hglobalDelta
      htGlobal hsmallScale hcanonicalMargin hparameter hft hf1Lower hf1Upper
      hf2 hf2Continuous hstripRadius q hq i hi hcoefficientLower hbudget
  refine ⟨C.graphRadius, ?_, C.htraceRadius⟩
  apply centeredTubeRectangle_tangent_to_other_of_commonStrip
    (fine.tubes i) (tubeAt q) f f1 f2 hf hf1 C
  · rfl
  · rfl

/-- Retained-good-pair form of the preceding theorem.  This is the direct
bridge consumed by coarse fibers: in the coefficient-lower branch, a
retained genuine Y1 incidence makes the active tube tangent to its assigned
literal coarse rectangle with the displayed budget. -/
theorem retainedY1Pair_coarseRectangle_tangent_of_coefficientLower
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (fine : UniformTubeFamily radius iota)
    (physical : FiniteProjectedShading (Real × Real) iota)
    (E : Set (Real × Real))
    (Y1 : FiniteProjectedShading (Real × Real) iota)
    (fineLabels : Finset fineLabel) (pointAt : fineLabel -> Real × Real)
    (centerTube : Tube radius) (tubeAt : Real × Real -> Tube radius)
    (f f1 f2 : Real -> Real) (outerA outerB : Real)
    (hOuter : outerA <= outerB)
    (hf : forall z, HasDerivAt f (f1 z) z)
    (hf1 : forall z, HasDerivAt f1 (f2 z) z)
    (tGlobal globalDelta fineT : Real)
    (facts : ActualCenteredHalfY1ActiveGeometryFacts fine physical E
      Y1.activeAtPoint tubeAt f f1 f2 outerA outerB hOuter hf hf1
      tGlobal globalDelta)
    (pointSource : ActualCenteredHalfPointRectangleSource E centerTube tubeAt
      f outerA outerB tGlobal)
    (hpointE : forall r, r ∈ fineLabels -> pointAt r ∈ E)
    {budgetFactor stripRadius : Real}
    (hwidth : (1 / 2 : Real) <= outerB - outerA)
    (hglobalDelta : 0 < globalDelta) (htGlobal : 0 < tGlobal)
    (hsmallScale :
      2 * globalDelta - (radius : Real) < tGlobal / 2400)
    (hcanonicalMargin :
      Real.sqrt (globalDelta / tGlobal) / 2 <=
        3 * (outerB - outerA) / 32)
    (hparameter : forall z, z ∈ Icc outerA outerB -> |z| <= 1)
    (hft : forall z, z ∈ Icc outerA outerB -> |f z| <= 2)
    (hf1Lower : forall z, z ∈ Icc outerA outerB -> 1 <= |f1 z|)
    (hf1Upper : forall z, z ∈ Icc outerA outerB -> |f1 z| <= 2)
    (hf2 : forall z, z ∈ Icc outerA outerB -> |f2 z| <= 1 / 100)
    (hf2Continuous : ContinuousOn f2 (Icc outerA outerB))
    (hstripRadius : 0 < stripRadius)
    (keep : iota -> fineLabel -> Prop) (i : iota) (r : fineLabel)
    (hpair : (i, r) ∈
      (y1FineCoarseRectangleData fine Y1 fineLabels pointAt tubeAt
        f f1 f2 hf hf1 (radius : Real) fineT globalDelta tGlobal).retainedGoodPairs
          keep)
    (hcoefficientLower :
      tGlobal / 2 <=
        tubePairCoefficientDistance (fine.tubes i) (tubeAt (pointAt r)))
    (hbudget :
      2 * stripRadius +
          (2 * (radius : Real) +
            (activeY1PointSlopeMargin (radius : Real) globalDelta tGlobal +
                30 * tGlobal *
                  (Real.sqrt (globalDelta / tGlobal) / 2)) *
              (Real.sqrt (globalDelta / tGlobal) / 2)) +
            (radius : Real) / 2 <=
        budgetFactor * globalDelta) :
    let D := y1FineCoarseRectangleData fine Y1 fineLabels pointAt tubeAt
      f f1 f2 hf hf1 (radius : Real) fineT globalDelta tGlobal
    exists graphRadius,
      (D.coarseRectangleAt r).carrier globalDelta ⊆
        cinematicVerticalNeighborhood
          (cinematicTraceValue f
            (tubeGraphA (fine.tubes i)) (tubeGraphB (fine.tubes i))
            (tubeGraphC (fine.tubes i)) (tubeGraphD (fine.tubes i)))
          (D.coarseRectangleAt r).rectangle.base
          (globalDelta + 2 * graphRadius) ∧
      2 * graphRadius + (radius : Real) / 2 <=
        budgetFactor * globalDelta := by
  dsimp only
  have hretained := y1FineCoarseRectangleData_retainedPair_active
    fine Y1 fineLabels pointAt tubeAt f f1 f2 hf hf1
      (radius : Real) fineT globalDelta tGlobal keep i r hpair
  have hqE : pointAt r ∈ E := hpointE r hretained.1
  simpa only [y1FineCoarseRectangleData] using
    activeY1_coarseRectangle_tangent_of_coefficientLower
      fine physical E Y1.activeAtPoint centerTube tubeAt f f1 f2 outerA
      outerB hOuter hf hf1 tGlobal globalDelta facts pointSource hwidth
      hglobalDelta htGlobal hsmallScale hcanonicalMargin hparameter hft
      hf1Lower hf1Upper hf2 hf2Continuous hstripRadius (pointAt r) hqE i
      hretained.2.1 hcoefficientLower hbudget

#print axioms centeredTubeC2GraphRectangle
#print axioms point_mem_centeredTubeC2GraphRectangle_carrier
#print axioms centeredTubeC2GraphRectangle_carrier_subset
#print axioms actualCenteredHalfY1FineCoarseRectangleData
#print axioms y1FineCoarseRectangleData_goodPair_iff
#print axioms y1FineCoarseRectangleData_retainedPair_active
#print axioms y1FineCoarseRectangleData_fine_carrier_subset_coarse
#print axioms centeredTubeC2GraphRectangle_carrier_eq_tubeNeighborhood
#print axioms retainedY1Pair_fine_coarse_membership_and_attainedTangency
#print axioms centeredTubeRectangle_tangent_to_other_of_commonStrip
#print axioms activeY1_coarseRectangle_tangent_of_coefficientLower
#print axioms retainedY1Pair_coarseRectangle_tangent_of_coefficientLower

end

end FamilyStickyCinematicL32Prop41ActualY1FineCoarseRectangleProducerV1
