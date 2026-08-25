import FamilyStickyGrounding.FamilyStickyWZ2TranslatedShadingUnionCovarianceV1
import FamilyStickyGrounding.FamilyStickyWZ2TubeCarrierCoordinateAdapterV1
import Submission.Kakeya.Uniformity.TubeFamily

set_option autoImplicit false

open MeasureTheory

namespace FamilyStickyWZ2TranslatedActualShadingInstantiationV1

open FamilyStickyWZ2ProjectionSliceRetentionV1
open FamilyStickyWZ2CinematicTranslationV1
open FamilyStickyWZ2TranslatedShadingUnionCovarianceV1
open FamilyStickyWZ2TubeCarrierCoordinateAdapterV1
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open LeanEval.Analysis.WangZahlKakeya

noncomputable section

/-!
# Actual WZ2 shading inputs under parameter-indexed translation copies

The source family below is a genuine project `UniformTubeFamily`, and `Y` is
a genuine `Shading` of its tube bodies.  WZ2's translated family is indexed
by `tau × kappa`: a translation-copy index and the original tube index.

The translated objects are deliberately exposed as carrier sets rather than
as `Tube delta`.  The ambient map contains the shear `y -> y + d0*z`; unless
`d0 = 0`, it is not an isometry and does not preserve the repository's exact
round-tube carrier at the same radius.  The parameter, carrier-union, and
twisted-projection covariance statements below are nevertheless exact.
-/

/-- Reduced `(a,b,d)` graph parameter extracted from an actual project tube.
The remaining graph slope `c` is fixed outside this triple in WZ2's `P_c`. -/
def tubeReducedLineParameter {delta : NNReal} (T : Tube delta) :
    ReducedLineParameter :=
  (tubeGraphA T, (tubeGraphB T, tubeGraphD T))

/-- The translated reduced parameter at product index `(copy, tube)`. -/
def indexedTranslatedTubeParameter
    {tau kappa : Type*} {delta : NNReal} [DecidableEq kappa]
    (shift : tau -> ReducedLineParameter)
    (fine : UniformTubeFamily delta kappa)
    (ji : tau × kappa) : ReducedLineParameter :=
  translateReducedLineParameter
    (shift ji.1).1 (shift ji.1).2.1 (shift ji.1).2.2
    (tubeReducedLineParameter (fine.tubes ji.2))

/-- Literal transported carrier of an actual source shading piece. -/
def indexedTranslatedActualShadingCarrier
    {tau kappa : Type*} {delta : NNReal} [DecidableEq kappa]
    (shift : tau -> ReducedLineParameter)
    (fine : UniformTubeFamily delta kappa)
    (Y : Shading (tubeBodyFamily fine.tubes))
    (ji : tau × kappa) : Set Space :=
  translatedShadingCarrier
    (shift ji.1).1 (shift ji.1).2.1 (shift ji.1).2.2
    Y.carrier ji.2

/-- The transported axis point has exactly the translated parameter claimed
by the paper, with its original `c` graph slope unchanged. -/
theorem ambientCinematicTranslation_actualTubeAxisPoint
    {tau kappa : Type*} {delta : NNReal} [DecidableEq kappa]
    (shift : tau -> ReducedLineParameter)
    (fine : UniformTubeFamily delta kappa)
    (j : tau) (i : kappa)
    (hvertical : (fine.tubes i).axis.direction 2 ≠ 0)
    (s : Real) :
    ambientCinematicTranslation
        (shift j).1 (shift j).2.1 (shift j).2.2
        ((fine.tubes i).axis.base +
          s • (fine.tubes i).axis.direction) =
      parameterLinePoint
        (indexedTranslatedTubeParameter shift fine (j, i)).1
        (indexedTranslatedTubeParameter shift fine (j, i)).2.1
        (tubeGraphC (fine.tubes i))
        (indexedTranslatedTubeParameter shift fine (j, i)).2.2
        (tubeAxisHeight (fine.tubes i) s) := by
  rw [tubeAxisPoint_eq_parameterLinePoint (fine.tubes i) hvertical s]
  simpa [indexedTranslatedTubeParameter, tubeReducedLineParameter,
    translateReducedLineParameter] using
    (ambientCinematicTranslation_parameterLinePoint
      (tubeGraphA (fine.tubes i)) (tubeGraphB (fine.tubes i))
      (tubeGraphC (fine.tubes i)) (tubeGraphD (fine.tubes i))
      (shift j).1 (shift j).2.1 (shift j).2.2
      (tubeAxisHeight (fine.tubes i) s))

/-- For one copy, the parameter range is the literal translate of the
original actual-tube parameter range. -/
theorem range_indexedTranslatedTubeParameter_fixedCopy
    {tau kappa : Type*} {delta : NNReal} [DecidableEq kappa]
    (shift : tau -> ReducedLineParameter)
    (fine : UniformTubeFamily delta kappa) (j : tau) :
    Set.range (fun i : kappa => indexedTranslatedTubeParameter shift fine (j, i)) =
      translateReducedLineParameter
          (shift j).1 (shift j).2.1 (shift j).2.2 ''
        Set.range (fun i : kappa => tubeReducedLineParameter (fine.tubes i)) := by
  ext p
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨tubeReducedLineParameter (fine.tubes i), ⟨i, rfl⟩, rfl⟩
  · rintro ⟨q, ⟨i, rfl⟩, rfl⟩
    exact ⟨i, rfl⟩

/-- The complete product-indexed parameter range is the union over copies.
Product indexing preserves repetitions even if two translated parameters
happen to coincide. -/
theorem range_indexedTranslatedTubeParameter
    {tau kappa : Type*} {delta : NNReal} [DecidableEq kappa]
    (shift : tau -> ReducedLineParameter)
    (fine : UniformTubeFamily delta kappa) :
    Set.range (indexedTranslatedTubeParameter shift fine) =
      ⋃ j, translateReducedLineParameter
          (shift j).1 (shift j).2.1 (shift j).2.2 ''
        Set.range (fun i : kappa => tubeReducedLineParameter (fine.tubes i)) := by
  ext p
  constructor
  · rintro ⟨⟨j, i⟩, rfl⟩
    apply Set.mem_iUnion.mpr
    exact ⟨j, ⟨tubeReducedLineParameter (fine.tubes i),
      ⟨i, rfl⟩, rfl⟩⟩
  · intro hp
    rcases Set.mem_iUnion.mp hp with ⟨j, q, ⟨i, rfl⟩, rfl⟩
    exact ⟨((j, i) : tau × kappa), rfl⟩

/-- A transported actual shading piece remains contained in the transported
carrier of its source tube.  This is the exact Tube-to-Shading provenance
available before constructing a distorted-tube adapter. -/
theorem indexedTranslatedActualShadingCarrier_subset_tubeImage
    {tau kappa : Type*} {delta : NNReal} [DecidableEq kappa]
    (shift : tau -> ReducedLineParameter)
    (fine : UniformTubeFamily delta kappa)
    (Y : Shading (tubeBodyFamily fine.tubes))
    (j : tau) (i : kappa) :
    indexedTranslatedActualShadingCarrier shift fine Y (j, i) ⊆
      ambientCinematicTranslation
          (shift j).1 (shift j).2.1 (shift j).2.2 ''
        (fine.tubes i).carrier := by
  exact Set.image_mono (Y.carrier_subset i)

/-- The product-indexed translated carrier union is the nested union of the
actual shading copies. -/
theorem iUnion_indexedTranslatedActualShadingCarrier
    {tau kappa : Type*} {delta : NNReal} [DecidableEq kappa]
    (shift : tau -> ReducedLineParameter)
    (fine : UniformTubeFamily delta kappa)
    (Y : Shading (tubeBodyFamily fine.tubes)) :
    (⋃ ji : tau × kappa,
        indexedTranslatedActualShadingCarrier shift fine Y ji) =
      ⋃ j, ⋃ i, translatedShadingCarrier
        (shift j).1 (shift j).2.1 (shift j).2.2 Y.carrier i := by
  ext p
  constructor
  · intro hp
    rcases Set.mem_iUnion.mp hp with ⟨⟨j, i⟩, hji⟩
    exact Set.mem_iUnion.mpr ⟨j, Set.mem_iUnion.mpr ⟨i, hji⟩⟩
  · intro hp
    rcases Set.mem_iUnion.mp hp with ⟨j, hj⟩
    rcases Set.mem_iUnion.mp hj with ⟨i, hi⟩
    exact Set.mem_iUnion.mpr ⟨(j, i), hi⟩

/-- The projected carrier union of one actual shading copy is exactly the
cinematic translation of the original projected shading union. -/
theorem twistedProjection_iUnion_actualShading_fixedCopy
    {tau kappa : Type*} {delta : NNReal} [DecidableEq kappa]
    (f : Real -> Real)
    (shift : tau -> ReducedLineParameter)
    (fine : UniformTubeFamily delta kappa)
    (Y : Shading (tubeBodyFamily fine.tubes)) (j : tau) :
    (⋃ i, twistedProjection f ''
        indexedTranslatedActualShadingCarrier shift fine Y (j, i)) =
      cinematicTranslation f
          (shift j).1 (shift j).2.1 (shift j).2.2 ''
        (⋃ i, twistedProjection f '' Y.carrier i) := by
  simpa [indexedTranslatedActualShadingCarrier] using
    (twistedProjection_iUnion_translatedShadingCarrier
      f (shift j).1 (shift j).2.1 (shift j).2.2 Y.carrier)

/-- The full translated projected union is the union over the exact
cinematic translates of the original actual shading union. -/
theorem twistedProjection_iUnion_actualShading
    {tau kappa : Type*} {delta : NNReal} [DecidableEq kappa]
    (f : Real -> Real)
    (shift : tau -> ReducedLineParameter)
    (fine : UniformTubeFamily delta kappa)
    (Y : Shading (tubeBodyFamily fine.tubes)) :
    (⋃ ji : tau × kappa, twistedProjection f ''
        indexedTranslatedActualShadingCarrier shift fine Y ji) =
      ⋃ j, cinematicTranslation f
          (shift j).1 (shift j).2.1 (shift j).2.2 ''
        (⋃ i, twistedProjection f '' Y.carrier i) := by
  ext q
  constructor
  · intro hq
    rcases Set.mem_iUnion.mp hq with ⟨⟨j, i⟩, hi⟩
    apply Set.mem_iUnion.mpr
    refine ⟨j, ?_⟩
    rw [← twistedProjection_iUnion_actualShading_fixedCopy
      f shift fine Y j]
    exact Set.mem_iUnion.mpr ⟨i, hi⟩
  · intro hq
    rcases Set.mem_iUnion.mp hq with ⟨j, hj⟩
    rw [← twistedProjection_iUnion_actualShading_fixedCopy
      f shift fine Y j] at hj
    rcases Set.mem_iUnion.mp hj with ⟨i, hi⟩
    exact Set.mem_iUnion.mpr ⟨(j, i), hi⟩

/-- Every fixed translated copy of the actual shading has exactly the same
projected area as the original copy. -/
theorem volume_twistedProjection_iUnion_actualShading_fixedCopy
    {tau kappa : Type*} {delta : NNReal} [DecidableEq kappa]
    (f : Real -> Real) (hf : Measurable f)
    (shift : tau -> ReducedLineParameter)
    (fine : UniformTubeFamily delta kappa)
    (Y : Shading (tubeBodyFamily fine.tubes)) (j : tau) :
    volume
        (⋃ i, twistedProjection f ''
          indexedTranslatedActualShadingCarrier shift fine Y (j, i)) =
      volume (⋃ i, twistedProjection f '' Y.carrier i) := by
  simpa [indexedTranslatedActualShadingCarrier] using
    (volume_twistedProjection_iUnion_translatedShadingCarrier
      f hf (shift j).1 (shift j).2.1 (shift j).2.2 Y.carrier)

/-- Any two translated copies of the actual shading have equal projected
area, the exact specialization of WZ2 equation `equivalenceOfUnions`. -/
theorem volume_twistedProjection_iUnion_actualShading_eq
    {tau kappa : Type*} {delta : NNReal} [DecidableEq kappa]
    (f : Real -> Real) (hf : Measurable f)
    (shift : tau -> ReducedLineParameter)
    (fine : UniformTubeFamily delta kappa)
    (Y : Shading (tubeBodyFamily fine.tubes)) (j k : tau) :
    volume
        (⋃ i, twistedProjection f ''
          indexedTranslatedActualShadingCarrier shift fine Y (j, i)) =
      volume
        (⋃ i, twistedProjection f ''
          indexedTranslatedActualShadingCarrier shift fine Y (k, i)) := by
  calc
    volume
          (⋃ i, twistedProjection f ''
            indexedTranslatedActualShadingCarrier shift fine Y (j, i)) =
        volume (⋃ i, twistedProjection f '' Y.carrier i) :=
      volume_twistedProjection_iUnion_actualShading_fixedCopy
        f hf shift fine Y j
    _ = volume
          (⋃ i, twistedProjection f ''
            indexedTranslatedActualShadingCarrier shift fine Y (k, i)) :=
      (volume_twistedProjection_iUnion_actualShading_fixedCopy
        f hf shift fine Y k).symm

#print axioms ambientCinematicTranslation_actualTubeAxisPoint
#print axioms range_indexedTranslatedTubeParameter_fixedCopy
#print axioms range_indexedTranslatedTubeParameter
#print axioms indexedTranslatedActualShadingCarrier_subset_tubeImage
#print axioms iUnion_indexedTranslatedActualShadingCarrier
#print axioms twistedProjection_iUnion_actualShading_fixedCopy
#print axioms twistedProjection_iUnion_actualShading
#print axioms volume_twistedProjection_iUnion_actualShading_fixedCopy
#print axioms volume_twistedProjection_iUnion_actualShading_eq

end
end FamilyStickyWZ2TranslatedActualShadingInstantiationV1
