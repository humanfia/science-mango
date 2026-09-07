import Family8Grounding.Family8KatzTaoFrostmanPropertiesV1
import FamilyStickyGrounding.Family6AffineConvexVolumeCoreV1
import Submission.Kakeya.ConvexFactoring.TubeHierarchyInfrastructure
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8GeneralizedFrostmanMultiplicityV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family4GlobalExtremalUpstream
open Family8KatzTaoFrostmanPropertiesV1

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false

/-!
# The deterministic rigid-copy part of generalized Frostman multiplicity

Lemma 3.9 of the streamlined Guth--Wang--Zahl paper applies `K_F(beta)` to
about `C_F(T)` randomly moved copies of a tube family.  Its probabilistic
input is Lemma 3.8: after random **rigid motions** and a bounded-multiplicity
refinement, the copied tubes are essentially distinct, retain the expected
cardinality, and have Frostman constant approximately one.

The existing sticky random-motion implementation selects ordinary
translations.  That implementation proves strong simultaneous load bounds,
but it has no rotation action and does not prove the cross-copy refinement or
the global Frostman conclusion from Lemma 3.8.  Translations alone cannot do
so for a highly parallel source family.

This file therefore formalizes the first missing, unconditional part of that
argument.  An arbitrary affine isometry acts on actual project tubes.  For a
finite family of such motions we construct the literal product-indexed tube
family and shading, and prove:

* exact tube-carrier and volume transport;
* preservation of `EssentiallyDistinct` inside each copy;
* exact copy factors for shading mass and summed family volume;
* exact preservation of shading density;
* the finite-copy union bound; and
* source average multiplicity is at most copied average multiplicity.

No good-motion event, Frostman bound, cardinality refinement, or final
multiplicity estimate is accepted as an input.  The remaining seam is exactly
the probabilistic rigid-motion/refinement conclusion of paper Lemma 3.8.
-/

/-- A genuine rigid motion of the ambient Euclidean space. -/
abbrev RigidMotion := Space ≃ᵃⁱ[Real] Space

/-- Every ambient rigid motion preserves Lebesgue volume. -/
theorem rigidMotion_measurePreserving (R : RigidMotion) :
    MeasurePreserving R volume volume := by
  have hlinear : MeasurePreserving R.linearIsometryEquiv volume volume :=
    LinearIsometryEquiv.measurePreserving R.linearIsometryEquiv
  have htranslate :
      MeasurePreserving (fun y : Space => R 0 + y) volume volume :=
    measurePreserving_add_left volume (R 0)
  have hcomposition := htranslate.comp hlinear
  convert hcomposition using 1
  funext x
  have hx : R x = R.linear x + R 0 :=
    congrFun (AffineMap.decomp R.toAffineEquiv.toAffineMap) x
  simpa only [Function.comp_apply, AffineIsometryEquiv.linear_eq_linear_isometry,
    LinearIsometryEquiv.coe_toLinearEquiv, add_comm] using hx

/-- Exact volume transport for every set.  The measurable-equivalence API
makes this valid without asking callers for a measurability side condition. -/
theorem volume_rigidMotion_image (R : RigidMotion) (s : Set Space) :
    volume (R '' s) = volume s := by
  have himage :
      R '' s = R.symm ⁻¹' s := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      change R.symm (R y) ∈ s
      simpa
    · intro hx
      change R.symm x ∈ s at hx
      exact ⟨R.symm x, hx, R.apply_symm_apply x⟩
  rw [himage]
  change volume
      ((R.symm.toHomeomorph.toMeasurableEquiv : Space → Space) ⁻¹' s) =
    volume s
  have hbase := rigidMotion_measurePreserving R.symm
  have hpres : MeasurePreserving
      (R.symm.toHomeomorph.toMeasurableEquiv : Space → Space)
      volume volume := by
    exact hbase.congr
      R.symm.toHomeomorph.toMeasurableEquiv.measurable
      (Filter.Eventually.of_forall fun _ => rfl)
  exact MeasurePreserving.measure_preimage_equiv
    (f := R.symm.toHomeomorph.toMeasurableEquiv) hpres s

/-- Apply a rigid motion to a parametrized unit segment. -/
def rigidUnitSegment (R : RigidMotion) (S : UnitSegment) : UnitSegment where
  base := R S.base
  direction := R.linearIsometryEquiv S.direction
  norm_direction := by
    rw [R.linearIsometryEquiv.norm_map, S.norm_direction]

@[simp]
theorem rigidUnitSegment_base (R : RigidMotion) (S : UnitSegment) :
    (rigidUnitSegment R S).base = R S.base :=
  rfl

@[simp]
theorem rigidUnitSegment_direction (R : RigidMotion) (S : UnitSegment) :
    (rigidUnitSegment R S).direction =
      R.linearIsometryEquiv S.direction :=
  rfl

@[simp]
theorem rigidUnitSegment_endpoint (R : RigidMotion) (S : UnitSegment) :
    (rigidUnitSegment R S).endpoint = R S.endpoint := by
  have hmap := R.map_vadd S.base S.direction
  simpa [UnitSegment.endpoint, rigidUnitSegment, add_comm] using hmap.symm

/-- Segment carriers are transported as literal images. -/
theorem rigidUnitSegment_carrier (R : RigidMotion) (S : UnitSegment) :
    (rigidUnitSegment R S).carrier = R '' S.carrier := by
  rw [UnitSegment.carrier, UnitSegment.carrier,
    rigidUnitSegment_base, rigidUnitSegment_endpoint]
  simpa only [AffineEquiv.coe_toAffineMap,
    AffineIsometryEquiv.coe_toAffineEquiv] using
      (image_segment Real R.toAffineEquiv.toAffineMap
        S.base S.endpoint).symm

/-- Closed metric thickenings commute with a surjective isometry. -/
theorem cthickening_rigidMotion (R : RigidMotion) (s : Set Space) (r : Real) :
    Metric.cthickening r (R '' s) = R '' Metric.cthickening r s := by
  ext x
  constructor
  · intro hx
    refine ⟨R.symm x, ?_, R.apply_symm_apply x⟩
    rw [Metric.mem_cthickening_iff] at hx ⊢
    calc
      Metric.infEDist (R.symm x) s =
          Metric.infEDist (R (R.symm x)) (R '' s) :=
        (Metric.infEDist_image R.isometry).symm
      _ = Metric.infEDist x (R '' s) := by rw [R.apply_symm_apply]
      _ ≤ ENNReal.ofReal r := hx
  · rintro ⟨y, hy, rfl⟩
    rw [Metric.mem_cthickening_iff] at hy ⊢
    rw [Metric.infEDist_image R.isometry]
    exact hy

/-- Apply a rigid motion to an actual project tube without changing radius. -/
def rigidTube {delta : NNReal} (R : RigidMotion) (T : Tube delta) :
    Tube delta where
  axis := rigidUnitSegment R T.axis

@[simp]
theorem rigidTube_axis {delta : NNReal} (R : RigidMotion) (T : Tube delta) :
    (rigidTube R T).axis = rigidUnitSegment R T.axis :=
  rfl

/-- The moved tube carrier is the literal rigid image of the source carrier. -/
theorem rigidTube_carrier {delta : NNReal}
    (R : RigidMotion) (T : Tube delta) :
    (rigidTube R T).carrier = R '' T.carrier := by
  unfold Tube.carrier rigidTube
  rw [rigidUnitSegment_carrier, cthickening_rigidMotion]

/-- Rigid motions preserve exact actual tube volume. -/
theorem rigidTube_volume {delta : NNReal}
    (R : RigidMotion) (T : Tube delta) :
    volume (rigidTube R T).carrier = volume T.carrier := by
  rw [rigidTube_carrier, volume_rigidMotion_image]

/-- Family4's literal half-overlap notion is invariant under a common rigid
motion. -/
theorem essentiallyDistinct_rigidTube_iff {delta : NNReal}
    (R : RigidMotion) (T U : Tube delta) :
    EssentiallyDistinct (rigidTube R T) (rigidTube R U) ↔
      EssentiallyDistinct T U := by
  unfold EssentiallyDistinct
  rw [rigidTube_carrier, rigidTube_carrier,
    ← Set.image_inter R.injective,
    volume_rigidMotion_image, volume_rigidMotion_image,
    volume_rigidMotion_image]

/-! ## Literal finite families of rigid copies -/

/-- Product-indexed actual tubes.  Occurrences are retained even if distinct
copy/index pairs happen to define the same geometric tube. -/
def indexedRigidCopyTubeFamily
    {tau iota : Type} {delta : NNReal}
    [Fintype tau] [DecidableEq tau] [Fintype iota] [DecidableEq iota]
    (motion : tau → RigidMotion) (F : UniformTubeFamily delta iota) :
    UniformTubeFamily delta (tau × iota) where
  tubes ji := rigidTube (motion ji.1) (F.tubes ji.2)
  refinement := UniformRefinement.ofFinset Finset.univ

@[simp]
theorem indexedRigidCopyTubeFamily_tubes
    {tau iota : Type} {delta : NNReal}
    [Fintype tau] [DecidableEq tau] [Fintype iota] [DecidableEq iota]
    (motion : tau → RigidMotion) (F : UniformTubeFamily delta iota)
    (ji : tau × iota) :
    (indexedRigidCopyTubeFamily motion F).tubes ji =
      rigidTube (motion ji.1) (F.tubes ji.2) :=
  rfl

/-- Literal transported shading on the product-indexed actual tubes. -/
def indexedRigidCopyShading
    {tau iota : Type} {delta : NNReal}
    [Fintype tau] [DecidableEq tau] [Fintype iota] [DecidableEq iota]
    (motion : tau → RigidMotion) (F : UniformTubeFamily delta iota)
    (Y : Shading F.bodyFamily) :
    Shading (indexedRigidCopyTubeFamily motion F).bodyFamily where
  carrier ji := motion ji.1 '' Y.carrier ji.2
  measurable_carrier ji :=
    (motion ji.1).toHomeomorph.toMeasurableEquiv.measurableSet_image.mpr
      (Y.measurable_carrier ji.2)
  carrier_subset ji := by
    rw [UniformTubeFamily.bodyFamily_apply, Tube.coe_body,
      indexedRigidCopyTubeFamily_tubes, rigidTube_carrier]
    exact Set.image_mono (Y.carrier_subset ji.2)

@[simp]
theorem indexedRigidCopyShading_carrier
    {tau iota : Type} {delta : NNReal}
    [Fintype tau] [DecidableEq tau] [Fintype iota] [DecidableEq iota]
    (motion : tau → RigidMotion) (F : UniformTubeFamily delta iota)
    (Y : Shading F.bodyFamily) (ji : tau × iota) :
    (indexedRigidCopyShading motion F Y).carrier ji =
      motion ji.1 '' Y.carrier ji.2 :=
  rfl

/-- Package the copied family and shading in Family8's actual datum type. -/
def indexedRigidCopyDatum
    {tau iota : Type} {delta : NNReal}
    [Fintype tau] [DecidableEq tau] [Fintype iota] [DecidableEq iota]
    (motion : tau → RigidMotion) (D : ActualTubeDatum delta iota) :
    ActualTubeDatum delta (tau × iota) where
  family := indexedRigidCopyTubeFamily motion D.family
  shading := indexedRigidCopyShading motion D.family D.shading

/-- Each individual rigid copy preserves pairwise essential distinctness.
This intentionally says nothing about pairs belonging to different copies. -/
theorem indexedRigidCopy_sameMotion_pairwise_essentiallyDistinct
    {tau iota : Type} {delta : NNReal}
    [Fintype tau] [DecidableEq tau] [Fintype iota] [DecidableEq iota]
    (motion : tau → RigidMotion) (D : ActualTubeDatum delta iota)
    (hD : D.IsAdmissible) (j : tau) :
    Set.Pairwise (Set.univ : Set iota) fun i k =>
      EssentiallyDistinct
        ((indexedRigidCopyDatum motion D).family.tubes (j, i))
        ((indexedRigidCopyDatum motion D).family.tubes (j, k)) := by
  intro i _hi k _hk hik
  change EssentiallyDistinct
      (rigidTube (motion j) (D.family.tubes i))
      (rigidTube (motion j) (D.family.tubes k))
  rw [essentiallyDistinct_rigidTube_iff]
  exact hD.pairwise_essentiallyDistinct (Set.mem_univ i)
    (Set.mem_univ k) hik

/-- Total shaded mass gains exactly the number of rigid copies. -/
theorem indexedRigidCopyShading_shadingMass
    {tau iota : Type} {delta : NNReal}
    [Fintype tau] [DecidableEq tau] [Fintype iota] [DecidableEq iota]
    (motion : tau → RigidMotion) (F : UniformTubeFamily delta iota)
    (Y : Shading F.bodyFamily) :
    (indexedRigidCopyShading motion F Y).shadingMass =
      (Fintype.card tau : ENNReal) * Y.shadingMass := by
  classical
  unfold Shading.shadingMass
  rw [Fintype.sum_prod_type]
  simp_rw [indexedRigidCopyShading_carrier, volume_rigidMotion_image]
  simp [nsmul_eq_mul]

/-- Summed actual tube volume gains the same exact copy factor. -/
theorem indexedRigidCopyTubeFamily_familyVolume
    {tau iota : Type} {delta : NNReal}
    [Fintype tau] [DecidableEq tau] [Fintype iota] [DecidableEq iota]
    (motion : tau → RigidMotion) (F : UniformTubeFamily delta iota) :
    familyVolume (indexedRigidCopyTubeFamily motion F).bodyFamily =
      (Fintype.card tau : ENNReal) * familyVolume F.bodyFamily := by
  classical
  unfold familyVolume
  rw [Fintype.sum_prod_type]
  simp_rw [UniformTubeFamily.bodyFamily_apply, Tube.coe_body,
    indexedRigidCopyTubeFamily_tubes, rigidTube_volume]
  simp [nsmul_eq_mul]

/-- Any nonempty finite rigid-copy family preserves shading density exactly. -/
theorem indexedRigidCopyShading_shadingDensity
    {tau iota : Type} {delta : NNReal}
    [Fintype tau] [Nonempty tau] [DecidableEq tau]
    [Fintype iota] [DecidableEq iota]
    (motion : tau → RigidMotion) (F : UniformTubeFamily delta iota)
    (Y : Shading F.bodyFamily) :
    (indexedRigidCopyShading motion F Y).shadingDensity =
      Y.shadingDensity := by
  unfold Shading.shadingDensity
  rw [indexedRigidCopyShading_shadingMass,
    indexedRigidCopyTubeFamily_familyVolume]
  apply ENNReal.mul_div_mul_left
  · exact_mod_cast
      (Fintype.card_pos_iff.mpr (inferInstance : Nonempty tau)).ne'
  · exact ENNReal.coe_ne_top

/-- The copied shaded union is exactly the union of rigid images of the
source shaded union. -/
theorem indexedRigidCopyShading_shadedUnion
    {tau iota : Type} {delta : NNReal}
    [Fintype tau] [DecidableEq tau] [Fintype iota] [DecidableEq iota]
    (motion : tau → RigidMotion) (F : UniformTubeFamily delta iota)
    (Y : Shading F.bodyFamily) :
    (indexedRigidCopyShading motion F Y).shadedUnion =
      ⋃ j : tau, motion j '' Y.shadedUnion := by
  ext x
  constructor
  · intro hx
    rcases Set.mem_iUnion.mp hx with ⟨⟨j, i⟩, hji⟩
    rcases hji with ⟨y, hy, rfl⟩
    apply Set.mem_iUnion.mpr
    exact ⟨j, y, Set.mem_iUnion.mpr ⟨i, hy⟩, rfl⟩
  · intro hx
    rcases Set.mem_iUnion.mp hx with ⟨j, y, hy, rfl⟩
    rcases Set.mem_iUnion.mp hy with ⟨i, hi⟩
    apply Set.mem_iUnion.mpr
    exact ⟨(j, i), y, hi, rfl⟩

/-- A finite family of rigid copies costs at most its literal cardinality in
shaded-union volume. -/
theorem volume_indexedRigidCopyShadingUnion_le_card_mul
    {tau iota : Type} {delta : NNReal}
    [Fintype tau] [DecidableEq tau] [Fintype iota] [DecidableEq iota]
    (motion : tau → RigidMotion) (F : UniformTubeFamily delta iota)
    (Y : Shading F.bodyFamily) :
    volume (indexedRigidCopyShading motion F Y).shadedUnion ≤
      (Fintype.card tau : ENNReal) * volume Y.shadedUnion := by
  rw [indexedRigidCopyShading_shadedUnion]
  calc
    volume (⋃ j : tau, motion j '' Y.shadedUnion) ≤
        ∑ j : tau, volume (motion j '' Y.shadedUnion) :=
      measure_iUnion_fintype_le volume _
    _ = ∑ _j : tau, volume Y.shadedUnion := by
      apply Finset.sum_congr rfl
      intro j _hj
      exact volume_rigidMotion_image (motion j) Y.shadedUnion
    _ = (Fintype.card tau : ENNReal) * volume Y.shadedUnion := by
      simp [nsmul_eq_mul]

/-- Adding a nonempty finite family of rigid copies cannot decrease average
multiplicity.  This is the deterministic inequality `mu(T) ≤ mu(T')` used in
paper Lemma 3.9. -/
theorem source_averageMultiplicity_le_indexedRigidCopy
    {tau iota : Type} {delta : NNReal}
    [Fintype tau] [Nonempty tau] [DecidableEq tau]
    [Fintype iota] [DecidableEq iota]
    (motion : tau → RigidMotion) (F : UniformTubeFamily delta iota)
    (Y : Shading F.bodyFamily) :
    Y.averageMultiplicity ≤
      (indexedRigidCopyShading motion F Y).averageMultiplicity := by
  let copies : ENNReal := Fintype.card tau
  have hcopies0 : copies ≠ 0 := by
    dsimp only [copies]
    exact_mod_cast
      (Fintype.card_pos_iff.mpr (inferInstance : Nonempty tau)).ne'
  have hcopiesTop : copies ≠ ∞ := ENNReal.coe_ne_top
  have hunion :=
    volume_indexedRigidCopyShadingUnion_le_card_mul motion F Y
  unfold Shading.averageMultiplicity
  rw [indexedRigidCopyShading_shadingMass]
  calc
    Y.shadingMass / volume Y.shadedUnion =
        (copies * Y.shadingMass) /
          (copies * volume Y.shadedUnion) :=
      (ENNReal.mul_div_mul_left Y.shadingMass (volume Y.shadedUnion)
        hcopies0 hcopiesTop).symm
    _ ≤ (copies * Y.shadingMass) /
          volume (indexedRigidCopyShading motion F Y).shadedUnion :=
      ENNReal.div_le_div_left hunion _

#print axioms rigidMotion_measurePreserving
#print axioms volume_rigidMotion_image
#print axioms rigidUnitSegment_carrier
#print axioms cthickening_rigidMotion
#print axioms rigidTube_carrier
#print axioms rigidTube_volume
#print axioms essentiallyDistinct_rigidTube_iff
#print axioms indexedRigidCopy_sameMotion_pairwise_essentiallyDistinct
#print axioms indexedRigidCopyShading_shadingMass
#print axioms indexedRigidCopyTubeFamily_familyVolume
#print axioms indexedRigidCopyShading_shadingDensity
#print axioms indexedRigidCopyShading_shadedUnion
#print axioms volume_indexedRigidCopyShadingUnion_le_card_mul
#print axioms source_averageMultiplicity_le_indexedRigidCopy

end

end Family8GeneralizedFrostmanMultiplicityV1
