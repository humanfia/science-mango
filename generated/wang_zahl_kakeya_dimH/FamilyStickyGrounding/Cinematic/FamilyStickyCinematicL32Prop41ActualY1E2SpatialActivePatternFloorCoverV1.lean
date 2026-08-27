import FamilyStickyRandomFiniteFloorParameterNetV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41ActualY1FineCoarseRectangleProducerV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000

open Set

namespace FamilyStickyCinematicL32Prop41ActualY1E2SpatialActivePatternFloorCoverV1

open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open FamilyStickyRandomFiniteFloorParameterNetV1
open FamilyStickyCinematicL32FiniteMeasurableIncidencePatternV1
open FamilyStickyCinematicL32FiniteMetricMaximalCoverV1
open FamilyStickyCinematicL32FiniteProjectedShadingMultiplicitySliceV1
open FamilyStickyCinematicL32FiniteIncidenceCanonicalCriticalCenterV1
open FamilyStickyCinematicL32FiniteIncidenceTangencyAfterNormCoverV1
open FamilyStickyCinematicL32ActualProjectedShadingCriticalFamilyV1
open FamilyStickyCinematicL32ActualProjectedNormSourceFamilyV1
open FamilyStickyCinematicL32ActualProjectedCenteredHalfTangencyStageV1
open FamilyStickyCinematicL32ActualProjectedCenteredHalfPointSourceV1
open FamilyStickyCinematicL32CenteredFractionIntervalsV1
open FamilyStickyCinematicL32Prop41ActualY1FineCoarseRectangleProducerV1
open FamilyStickyCinematicL32RectangleTangencyV1
open FamilyStickyCinematicL32TubePairTraceV1
open FamilyStickyWZ2TubeCarrierCoordinateAdapterV1

noncomputable section

universe u

/-!
# Spatial active-pattern floor cover for the actual E2 carrier

The existing finite metric maximal cover is a cover of a finite tube family in
coefficient space.  It is not a cover of continuum points.  Here a continuum
source point is coded by its finite active-incidence pattern and by a one
dimensional floor cell for its vertical parameter.  Every occupied code keeps
an actual source representative.

Equal codes force the selected tube to agree whenever the selector is a
function of the active pattern, while the vertical parameters differ by less
than one mesh.  Consequently every source point lies in the fine graph
rectangle centred at its code representative.  This is the literal finite
cover required by the measurable first-hit Y2 partition.
-/

/-- A code consists of a finite active pattern and one vertical floor label. -/
abbrev SpatialActivePatternCode (iota : Type u) := Finset iota × Int

/-- Raw code of a continuum point. -/
def spatialActivePatternRawCode
    {iota : Type u} [DecidableEq iota]
    (patternAt : Real × Real -> Finset iota) (mesh : Real)
    (q : Real × Real) : SpatialActivePatternCode iota :=
  (patternAt q, Int.floor (q.2 / mesh))

/-- Explicit finite box containing all codes with pattern inside ambient and
vertical coordinate in the absolute unit interval. -/
noncomputable def spatialActivePatternAllCodes
    {iota : Type u} [DecidableEq iota]
    (ambient : Finset iota) (mesh : Real) :
    Finset (SpatialActivePatternCode iota) := by
  classical
  exact ambient.powerset.product (codeInterval mesh 1)

/-- Codes actually occupied by the source set. -/
noncomputable def spatialActivePatternOccupiedCodes
    {iota : Type u} [DecidableEq iota]
    (ambient : Finset iota) (patternAt : Real × Real -> Finset iota)
    (source : Set (Real × Real)) (mesh : Real) :
    Finset (SpatialActivePatternCode iota) := by
  classical
  exact (spatialActivePatternAllCodes ambient mesh).filter fun c =>
    exists q, q ∈ source ∧ spatialActivePatternRawCode patternAt mesh q = c

/-- Finite label type of occupied spatial active-pattern codes. -/
abbrev SpatialActivePatternLabel
    {iota : Type u} [DecidableEq iota]
    (ambient : Finset iota) (patternAt : Real × Real -> Finset iota)
    (source : Set (Real × Real)) (mesh : Real) :=
  FiniteMetricMember
    (spatialActivePatternOccupiedCodes ambient patternAt source mesh)

@[simp]
theorem mem_spatialActivePatternOccupiedCodes_iff
    {iota : Type u} [DecidableEq iota]
    (ambient : Finset iota) (patternAt : Real × Real -> Finset iota)
    (source : Set (Real × Real)) (mesh : Real)
    (c : SpatialActivePatternCode iota) :
    c ∈ spatialActivePatternOccupiedCodes ambient patternAt source mesh <->
      c ∈ spatialActivePatternAllCodes ambient mesh ∧
        exists q, q ∈ source ∧
          spatialActivePatternRawCode patternAt mesh q = c := by
  classical
  simp [spatialActivePatternOccupiedCodes]

theorem spatialActivePatternRawCode_mem_allCodes
    {iota : Type u} [DecidableEq iota]
    (ambient : Finset iota) (patternAt : Real × Real -> Finset iota)
    {mesh : Real} (hmesh : 0 < mesh) (q : Real × Real)
    (hpattern : patternAt q ⊆ ambient) (hy : |q.2| ≤ 1) :
    spatialActivePatternRawCode patternAt mesh q ∈
      spatialActivePatternAllCodes ambient mesh := by
  classical
  change (patternAt q, Int.floor (q.2 / mesh)) ∈
    ambient.powerset.product (codeInterval mesh 1)
  apply Finset.mem_product.mpr
  refine ⟨Finset.mem_powerset.mpr hpattern, ?_⟩
  rw [codeInterval, Finset.mem_Icc]
  constructor
  · apply Int.floor_le_floor
    apply (div_le_div_iff_of_pos_right hmesh).2
    exact neg_le_of_abs_le hy
  · apply Int.floor_le_floor
    apply (div_le_div_iff_of_pos_right hmesh).2
    exact le_of_abs_le hy

/-- Actual source representative stored by one occupied code. -/
noncomputable def spatialActivePatternRepresentative
    {iota : Type u} [DecidableEq iota]
    (ambient : Finset iota) (patternAt : Real × Real -> Finset iota)
    (source : Set (Real × Real)) (mesh : Real)
    (r : SpatialActivePatternLabel ambient patternAt source mesh) :
    Real × Real :=
  Classical.choose
    ((mem_spatialActivePatternOccupiedCodes_iff
      ambient patternAt source mesh r.1).mp r.2).2

theorem spatialActivePatternRepresentative_spec
    {iota : Type u} [DecidableEq iota]
    (ambient : Finset iota) (patternAt : Real × Real -> Finset iota)
    (source : Set (Real × Real)) (mesh : Real)
    (r : SpatialActivePatternLabel ambient patternAt source mesh) :
    spatialActivePatternRepresentative ambient patternAt source mesh r ∈
        source ∧
      spatialActivePatternRawCode patternAt mesh
          (spatialActivePatternRepresentative
            ambient patternAt source mesh r) = r.1 :=
  Classical.choose_spec
    ((mem_spatialActivePatternOccupiedCodes_iff
      ambient patternAt source mesh r.1).mp r.2).2

/-- The occupied label assigned to a bounded source point. -/
noncomputable def spatialActivePatternOwnLabel
    {iota : Type u} [DecidableEq iota]
    (ambient : Finset iota) (patternAt : Real × Real -> Finset iota)
    (source : Set (Real × Real)) {mesh : Real} (hmesh : 0 < mesh)
    (q : Real × Real) (hq : q ∈ source)
    (hpattern : patternAt q ⊆ ambient) (hy : |q.2| ≤ 1) :
    SpatialActivePatternLabel ambient patternAt source mesh :=
  ⟨spatialActivePatternRawCode patternAt mesh q,
    (mem_spatialActivePatternOccupiedCodes_iff
      ambient patternAt source mesh
        (spatialActivePatternRawCode patternAt mesh q)).mpr
      ⟨spatialActivePatternRawCode_mem_allCodes ambient patternAt hmesh q
          hpattern hy,
        ⟨q, hq, rfl⟩⟩⟩

theorem spatialActivePatternRepresentative_ownLabel_mem
    {iota : Type u} [DecidableEq iota]
    (ambient : Finset iota) (patternAt : Real × Real -> Finset iota)
    (source : Set (Real × Real)) {mesh : Real} (hmesh : 0 < mesh)
    (q : Real × Real) (hq : q ∈ source)
    (hpattern : patternAt q ⊆ ambient) (hy : |q.2| ≤ 1) :
    spatialActivePatternRepresentative ambient patternAt source mesh
        (spatialActivePatternOwnLabel ambient patternAt source hmesh q hq
          hpattern hy) ∈ source :=
  (spatialActivePatternRepresentative_spec ambient patternAt source mesh
    (spatialActivePatternOwnLabel ambient patternAt source hmesh q hq
      hpattern hy)).1

theorem spatialActivePatternRepresentative_ownLabel_code
    {iota : Type u} [DecidableEq iota]
    (ambient : Finset iota) (patternAt : Real × Real -> Finset iota)
    (source : Set (Real × Real)) {mesh : Real} (hmesh : 0 < mesh)
    (q : Real × Real) (hq : q ∈ source)
    (hpattern : patternAt q ⊆ ambient) (hy : |q.2| ≤ 1) :
    spatialActivePatternRawCode patternAt mesh
        (spatialActivePatternRepresentative ambient patternAt source mesh
          (spatialActivePatternOwnLabel ambient patternAt source hmesh q hq
            hpattern hy)) =
      spatialActivePatternRawCode patternAt mesh q := by
  simpa only [spatialActivePatternOwnLabel] using
    (spatialActivePatternRepresentative_spec ambient patternAt source mesh
      (spatialActivePatternOwnLabel ambient patternAt source hmesh q hq
        hpattern hy)).2

theorem spatialActivePatternRepresentative_ownLabel_pattern
    {iota : Type u} [DecidableEq iota]
    (ambient : Finset iota) (patternAt : Real × Real -> Finset iota)
    (source : Set (Real × Real)) {mesh : Real} (hmesh : 0 < mesh)
    (q : Real × Real) (hq : q ∈ source)
    (hpattern : patternAt q ⊆ ambient) (hy : |q.2| ≤ 1) :
    patternAt
        (spatialActivePatternRepresentative ambient patternAt source mesh
          (spatialActivePatternOwnLabel ambient patternAt source hmesh q hq
            hpattern hy)) =
      patternAt q := by
  exact congrArg Prod.fst
    (spatialActivePatternRepresentative_ownLabel_code ambient patternAt
      source hmesh q hq hpattern hy)

theorem abs_vertical_sub_spatialActivePatternRepresentative_ownLabel_lt
    {iota : Type u} [DecidableEq iota]
    (ambient : Finset iota) (patternAt : Real × Real -> Finset iota)
    (source : Set (Real × Real)) {mesh : Real} (hmesh : 0 < mesh)
    (q : Real × Real) (hq : q ∈ source)
    (hpattern : patternAt q ⊆ ambient) (hy : |q.2| ≤ 1) :
    |q.2 -
        (spatialActivePatternRepresentative ambient patternAt source mesh
          (spatialActivePatternOwnLabel ambient patternAt source hmesh q hq
            hpattern hy)).2| < mesh := by
  have hcode :=
    spatialActivePatternRepresentative_ownLabel_code ambient patternAt
      source hmesh q hq hpattern hy
  have hfloor :
      Int.floor (q.2 / mesh) =
        Int.floor
          ((spatialActivePatternRepresentative ambient patternAt source mesh
            (spatialActivePatternOwnLabel ambient patternAt source hmesh q hq
              hpattern hy)).2 / mesh) := by
    exact congrArg Prod.snd hcode |>.symm
  have hscaled :
      |q.2 / mesh -
        (spatialActivePatternRepresentative ambient patternAt source mesh
          (spatialActivePatternOwnLabel ambient patternAt source hmesh q hq
            hpattern hy)).2 / mesh| < 1 :=
    Int.abs_sub_lt_one_of_floor_eq_floor hfloor
  rw [← sub_div, abs_div, abs_of_pos hmesh] at hscaled
  exact (div_lt_one hmesh).mp hscaled

/-- Explicit count of all occupied spatial active-pattern labels. -/
theorem card_spatialActivePatternLabel_le
    {iota : Type u} [DecidableEq iota]
    (ambient : Finset iota) (patternAt : Real × Real -> Finset iota)
    (source : Set (Real × Real)) (mesh : Real) :
    Fintype.card (SpatialActivePatternLabel ambient patternAt source mesh) ≤
      2 ^ ambient.card *
        ((Int.floor (1 / mesh) + 1 -
          Int.floor (-1 / mesh)).toNat) := by
  classical
  calc
    Fintype.card (SpatialActivePatternLabel ambient patternAt source mesh) =
        (spatialActivePatternOccupiedCodes
          ambient patternAt source mesh).card := Fintype.card_coe _
    _ ≤ (spatialActivePatternAllCodes ambient mesh).card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    _ = ambient.powerset.card * (codeInterval mesh 1).card := by
      simp [spatialActivePatternAllCodes]
    _ = 2 ^ ambient.card *
        ((Int.floor (1 / mesh) + 1 -
          Int.floor (-1 / mesh)).toNat) := by
      rw [Finset.card_powerset]
      simp only [codeInterval, Int.card_Icc]

/-- Every source point lies in the fine rectangle of its occupied code. -/
theorem exists_spatialActivePattern_fineRectangle_cover
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    (fine : UniformTubeFamily radius iota)
    (Y1 : FiniteProjectedShading (Real × Real) iota)
    (ambient : Finset iota)
    (patternAt : Real × Real -> Finset iota)
    (source : Set (Real × Real)) {mesh : Real}
    (hmesh : 0 < mesh)
    (hpattern : ∀ q ∈ source, patternAt q ⊆ ambient)
    (hy : ∀ q ∈ source, |q.2| ≤ 1)
    (tubeAt : Real × Real -> Tube radius)
    (htubePattern : ∀ q ∈ source, ∀ r ∈ source,
      patternAt q = patternAt r -> tubeAt q = tubeAt r)
    (f f1 f2 : Real -> Real)
    (hf : ∀ z, HasDerivAt f (f1 z) z)
    (hf1 : ∀ z, HasDerivAt f1 (f2 z) z)
    (fineDelta fineT coarseDelta coarseT : Real)
    (hmeshBase : mesh ≤ Real.sqrt (fineDelta / fineT) / 2)
    (hpointTube : ∀ q ∈ source,
      |q.1 - cinematicTraceValue f
        (tubeGraphA (tubeAt q)) (tubeGraphB (tubeAt q))
        (tubeGraphC (tubeAt q)) (tubeGraphD (tubeAt q)) q.2| ≤ fineDelta)
    (q : Real × Real) (hq : q ∈ source) :
    let fineLabels : Finset
      (SpatialActivePatternLabel ambient patternAt source mesh) := Finset.univ
    let pointAt := spatialActivePatternRepresentative
      ambient patternAt source mesh
    let D := y1FineCoarseRectangleData fine Y1 fineLabels pointAt tubeAt
      f f1 f2 hf hf1 fineDelta fineT coarseDelta coarseT
    exists r, r ∈ fineLabels ∧
      q ∈ (D.fineRectangleAt r).carrier fineDelta := by
  classical
  dsimp only
  let r := spatialActivePatternOwnLabel ambient patternAt source hmesh q hq
    (hpattern q hq) (hy q hq)
  let representative := spatialActivePatternRepresentative
    ambient patternAt source mesh r
  have hrepresentativeSource : representative ∈ source := by
    exact spatialActivePatternRepresentative_ownLabel_mem ambient patternAt
      source hmesh q hq (hpattern q hq) (hy q hq)
  have hpatternEq : patternAt representative = patternAt q := by
    exact spatialActivePatternRepresentative_ownLabel_pattern ambient patternAt
      source hmesh q hq (hpattern q hq) (hy q hq)
  have htubeEq : tubeAt representative = tubeAt q :=
    htubePattern representative hrepresentativeSource q hq hpatternEq
  have hyClose : |q.2 - representative.2| < mesh := by
    exact abs_vertical_sub_spatialActivePatternRepresentative_ownLabel_lt
      ambient patternAt source hmesh q hq (hpattern q hq) (hy q hq)
  refine ⟨r, Finset.mem_univ r, ?_⟩
  change q ∈
    (centeredTubeC2GraphRectangle (tubeAt representative) f f1 f2 hf hf1
      representative.2 fineDelta fineT).carrier fineDelta
  refine ⟨?_, ?_⟩
  · change q.2 ∈ Icc
      (representative.2 - Real.sqrt (fineDelta / fineT) / 2)
      (representative.2 + Real.sqrt (fineDelta / fineT) / 2)
    have hyBounds := abs_lt.mp hyClose
    constructor <;> linarith
  · rw [htubeEq]
    exact hpointTube q hq

/-- Set-level form consumed directly by the finite first-hit partition. -/
theorem spatialActivePattern_fineRectangle_cover
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    (fine : UniformTubeFamily radius iota)
    (Y1 : FiniteProjectedShading (Real × Real) iota)
    (ambient : Finset iota)
    (patternAt : Real × Real -> Finset iota)
    (source : Set (Real × Real)) {mesh : Real}
    (hmesh : 0 < mesh)
    (hpattern : ∀ q ∈ source, patternAt q ⊆ ambient)
    (hy : ∀ q ∈ source, |q.2| ≤ 1)
    (tubeAt : Real × Real -> Tube radius)
    (htubePattern : ∀ q ∈ source, ∀ r ∈ source,
      patternAt q = patternAt r -> tubeAt q = tubeAt r)
    (f f1 f2 : Real -> Real)
    (hf : ∀ z, HasDerivAt f (f1 z) z)
    (hf1 : ∀ z, HasDerivAt f1 (f2 z) z)
    (fineDelta fineT coarseDelta coarseT : Real)
    (hmeshBase : mesh ≤ Real.sqrt (fineDelta / fineT) / 2)
    (hpointTube : ∀ q ∈ source,
      |q.1 - cinematicTraceValue f
        (tubeGraphA (tubeAt q)) (tubeGraphB (tubeAt q))
        (tubeGraphC (tubeAt q)) (tubeGraphD (tubeAt q)) q.2| ≤ fineDelta) :
    let fineLabels : Finset
      (SpatialActivePatternLabel ambient patternAt source mesh) := Finset.univ
    let pointAt := spatialActivePatternRepresentative
      ambient patternAt source mesh
    let D := y1FineCoarseRectangleData fine Y1 fineLabels pointAt tubeAt
      f f1 f2 hf hf1 fineDelta fineT coarseDelta coarseT
    ∀ q, q ∈ source -> exists r, r ∈ fineLabels ∧
      q ∈ (D.fineRectangleAt r).carrier fineDelta := by
  dsimp only
  intro q hq
  exact exists_spatialActivePattern_fineRectangle_cover fine Y1 ambient
    patternAt source hmesh hpattern hy tubeAt htubePattern
    f f1 f2 hf hf1 fineDelta fineT coarseDelta coarseT hmeshBase
    hpointTube q hq

/-- The actual centered-half selector is literally a function of the physical
active pattern. -/
theorem actualProjectedCenteredHalfTangencyCenterTubeAt_eq_of_active_eq
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    (fine : UniformTubeFamily radius iota)
    (physical : FiniteProjectedShading (Real × Real) iota)
    (f f1 f2 : Real -> Real) (outerA outerB : Real)
    (hOuter : outerA ≤ outerB)
    (hf : ∀ z, HasDerivAt f (f1 z) z)
    (hf1 : ∀ z, HasDerivAt f1 (f2 z) z)
    (globalScale : Real) (globalCenter : Tube radius)
    (ceiling exponent : Real) (q r : Real × Real)
    (hactive : physical.activeAtPoint q = physical.activeAtPoint r) :
    actualProjectedCenteredHalfTangencyCenterTubeAt fine physical
        f f1 f2 outerA outerB hOuter hf hf1 globalScale globalCenter
        ceiling exponent q =
      actualProjectedCenteredHalfTangencyCenterTubeAt fine physical
        f f1 f2 outerA outerB hOuter hf hf1 globalScale globalCenter
        ceiling exponent r := by
  simp only [actualProjectedCenteredHalfTangencyCenterTubeAt,
    finiteIncidenceLocalizedTangencyCenter,
    finiteIncidenceCriticalCenter]
  rw [show finiteIncidenceActiveAtPoint physical.ambient
      (fun i x => x ∈ physical.carrier i) q =
        finiteIncidenceActiveAtPoint physical.ambient
          (fun i x => x ∈ physical.carrier i) r by
    simpa only [FiniteProjectedShading.activeAtPoint] using hactive]

/-- Actual spatial cover using the existing point-source package. -/
theorem actualCenteredHalfPointSource_spatialActivePattern_fineRectangle_cover
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    (fine : UniformTubeFamily radius iota)
    (physical Y1 : FiniteProjectedShading (Real × Real) iota)
    (source : Set (Real × Real)) {mesh : Real}
    (hmesh : 0 < mesh)
    (f f1 f2 : Real -> Real) (outerA outerB : Real)
    (hOuter : outerA ≤ outerB)
    (hf : ∀ z, HasDerivAt f (f1 z) z)
    (hf1 : ∀ z, HasDerivAt f1 (f2 z) z)
    (globalScale : Real) (globalCenter : Tube radius)
    (ceiling exponent : Real)
    (pointSource : ActualCenteredHalfPointRectangleSource source globalCenter
      (actualProjectedCenteredHalfTangencyCenterTubeAt fine physical
        f f1 f2 outerA outerB hOuter hf hf1 globalScale globalCenter
        ceiling exponent)
      f outerA outerB globalScale)
    (hparameter : ∀ z, z ∈ Icc outerA outerB -> |z| ≤ 1)
    (fineT coarseDelta coarseT : Real)
    (hmeshBase : mesh ≤ Real.sqrt ((radius : Real) / fineT) / 2) :
    let patternAt := physical.activeAtPoint
    let fineLabels : Finset
      (SpatialActivePatternLabel physical.ambient patternAt source mesh) :=
        Finset.univ
    let pointAt := spatialActivePatternRepresentative
      physical.ambient patternAt source mesh
    let tubeAt := actualProjectedCenteredHalfTangencyCenterTubeAt fine physical
      f f1 f2 outerA outerB hOuter hf hf1 globalScale globalCenter
      ceiling exponent
    let D := y1FineCoarseRectangleData fine Y1 fineLabels pointAt tubeAt
      f f1 f2 hf hf1 (radius : Real) fineT coarseDelta coarseT
    ∀ q, q ∈ source -> exists r, r ∈ fineLabels ∧
      q ∈ (D.fineRectangleAt r).carrier (radius : Real) := by
  dsimp only
  apply spatialActivePattern_fineRectangle_cover fine Y1 physical.ambient
    physical.activeAtPoint source hmesh
  · intro q _hq
    exact finiteIncidenceActiveAtPoint_subset physical.ambient
      (fun i x => x ∈ physical.carrier i) q
  · intro q hq
    have htheta := pointSource.hpointTheta q hq
    apply hparameter q.2
    rcases htheta with ⟨hthetaLeft, hthetaRight⟩
    constructor <;>
      simp only [centeredFractionLeft,
        centeredFractionRight] at hthetaLeft hthetaRight ⊢ <;>
      linarith
  · intro q hq r hr hactive
    exact actualProjectedCenteredHalfTangencyCenterTubeAt_eq_of_active_eq
      fine physical f f1 f2 outerA outerB hOuter hf hf1 globalScale
      globalCenter ceiling exponent q r hactive
  · exact hmeshBase
  · exact pointSource.hpointTube

#print axioms spatialActivePatternRepresentative_spec
#print axioms spatialActivePatternRepresentative_ownLabel_pattern
#print axioms abs_vertical_sub_spatialActivePatternRepresentative_ownLabel_lt
#print axioms card_spatialActivePatternLabel_le
#print axioms spatialActivePattern_fineRectangle_cover
#print axioms actualProjectedCenteredHalfTangencyCenterTubeAt_eq_of_active_eq
#print axioms actualCenteredHalfPointSource_spatialActivePattern_fineRectangle_cover

end

end FamilyStickyCinematicL32Prop41ActualY1E2SpatialActivePatternFloorCoverV1
