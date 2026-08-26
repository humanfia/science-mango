import FamilyStickyGrounding.FamilyStickyConvexBodyTranslationConcentrationV1
import FamilyStickyGrounding.FamilyStickyHierarchyTerminalEssentialDistinctAdapterV1
import Submission.Kakeya.ConvexGeometry.Shading

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 3000000

open Set MeasureTheory
open scoped ENNReal NNReal Pointwise

namespace FamilyStickyHierarchyEuclideanTranslatedShadingBridgeV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open FamilyStickyActualTubeTranslationV1
open FamilyStickyConvexBodyTranslationConcentrationV1
open FamilyStickyHierarchyRandomMotionAdapterV1
open FamilyStickyHierarchyRandomMotionAdapterV1.HierarchyRandomMotionGeometry
open FamilyStickyHierarchyJointRandomMotionCertificateV1
open FamilyStickyHierarchyTerminalEssentialDistinctAdapterV1

noncomputable section

/-!
# Euclidean translated shadings for hierarchy terminal copies

The hierarchy random-motion output acts on ambient `Space` by ordinary
translation.  This file constructs the resulting product-indexed convex
family and shading literally, and proves the finite-copy union loss from Haar
invariance.  No union comparison or shading-validity callback is assumed.

This is deliberately separate from the WZ2 cinematic action
`(x,y,z) |-> (x+a,y+b+d*z,z)`: a hierarchy motion is an arbitrary vector in
`Space`, and can in particular move the third coordinate.
-/

universe u v

/-! ## Generic finite families of Euclidean translates -/

/-- All ordinary Euclidean translates of an indexed convex family, retaining
the product occurrence index even when two translated bodies coincide. -/
def indexedEuclideanTranslatedBodyFamily
    {tau : Type u} {kappa : Type v}
    (shift : tau -> Space) (F : ConvexFamily kappa) :
    ConvexFamily (tau × kappa) :=
  fun ji => translateConvexBody (F ji.2) (shift ji.1)

@[simp]
theorem coe_indexedEuclideanTranslatedBodyFamily
    {tau : Type u} {kappa : Type v}
    (shift : tau -> Space) (F : ConvexFamily kappa)
    (ji : tau × kappa) :
    (indexedEuclideanTranslatedBodyFamily shift F ji : Set Space) =
      (fun x => shift ji.1 + x) '' (F ji.2 : Set Space) :=
  rfl

/-- Literal translated carriers form a genuine shading of the literal
translated convex bodies. -/
def indexedEuclideanTranslatedShading
    {tau : Type u} {kappa : Type v}
    (shift : tau -> Space) (F : ConvexFamily kappa) (Y : Shading F) :
    Shading (indexedEuclideanTranslatedBodyFamily shift F) where
  carrier ji := (fun x => shift ji.1 + x) '' Y.carrier ji.2
  measurable_carrier ji :=
    (MeasurableEquiv.addLeft (shift ji.1)).measurableSet_image.mpr
      (Y.measurable_carrier ji.2)
  carrier_subset ji := Set.image_mono (Y.carrier_subset ji.2)

@[simp]
theorem indexedEuclideanTranslatedShading_carrier
    {tau : Type u} {kappa : Type v}
    (shift : tau -> Space) (F : ConvexFamily kappa) (Y : Shading F)
    (ji : tau × kappa) :
    (indexedEuclideanTranslatedShading shift F Y).carrier ji =
      (fun x => shift ji.1 + x) '' Y.carrier ji.2 :=
  rfl

theorem volume_euclideanTranslate_image
    (v : Space) (s : Set Space) :
    volume ((fun x => v + x) '' s) = volume s := by
  change volume (v +ᵥ s) = volume s
  exact MeasureTheory.measure_vadd volume v s

/-- Total shading mass gains exactly the number of copies. -/
theorem indexedEuclideanTranslatedShading_shadingMass
    {tau : Type u} {kappa : Type v}
    [Fintype tau] [Fintype kappa]
    (shift : tau -> Space) (F : ConvexFamily kappa) (Y : Shading F) :
    (indexedEuclideanTranslatedShading shift F Y).shadingMass =
      (Fintype.card tau : ENNReal) * Y.shadingMass := by
  classical
  unfold Shading.shadingMass
  rw [Fintype.sum_prod_type]
  simp_rw [indexedEuclideanTranslatedShading_carrier,
    volume_euclideanTranslate_image]
  simp [nsmul_eq_mul]

/-- Summed convex-family volume gains the same exact copy factor. -/
theorem indexedEuclideanTranslatedBodyFamily_familyVolume
    {tau : Type u} {kappa : Type v}
    [Fintype tau] [Fintype kappa]
    (shift : tau -> Space) (F : ConvexFamily kappa) :
    familyVolume (indexedEuclideanTranslatedBodyFamily shift F) =
      (Fintype.card tau : ENNReal) * familyVolume F := by
  classical
  unfold familyVolume
  rw [Fintype.sum_prod_type]
  simp_rw [coe_indexedEuclideanTranslatedBodyFamily,
    volume_euclideanTranslate_image]
  simp [nsmul_eq_mul]

/-- A nonempty finite collection of Euclidean copies preserves shading
density exactly. -/
theorem indexedEuclideanTranslatedShading_shadingDensity
    {tau : Type u} {kappa : Type v}
    [Fintype tau] [Nonempty tau] [Fintype kappa]
    (shift : tau -> Space) (F : ConvexFamily kappa) (Y : Shading F) :
    (indexedEuclideanTranslatedShading shift F Y).shadingDensity =
      Y.shadingDensity := by
  unfold Shading.shadingDensity
  rw [indexedEuclideanTranslatedShading_shadingMass,
    indexedEuclideanTranslatedBodyFamily_familyVolume]
  apply ENNReal.mul_div_mul_left
  · exact_mod_cast
      (Fintype.card_pos_iff.mpr (inferInstance : Nonempty tau)).ne'
  · exact ENNReal.coe_ne_top

/-- The product-indexed shaded union is exactly the union of ordinary
translates of the source shaded union. -/
theorem indexedEuclideanTranslatedShading_shadedUnion
    {tau : Type u} {kappa : Type v}
    (shift : tau -> Space) (F : ConvexFamily kappa) (Y : Shading F) :
    (indexedEuclideanTranslatedShading shift F Y).shadedUnion =
      ⋃ j : tau, (fun x => shift j + x) '' Y.shadedUnion := by
  ext p
  constructor
  · intro hp
    rcases Set.mem_iUnion.mp hp with ⟨⟨j, i⟩, hji⟩
    rcases hji with ⟨q, hq, rfl⟩
    apply Set.mem_iUnion.mpr
    refine ⟨j, q, ?_, rfl⟩
    exact Set.mem_iUnion.mpr ⟨i, hq⟩
  · intro hp
    rcases Set.mem_iUnion.mp hp with ⟨j, q, hq, rfl⟩
    rcases Set.mem_iUnion.mp hq with ⟨i, hi⟩
    apply Set.mem_iUnion.mpr
    exact ⟨(j, i), q, hi, rfl⟩

/-- Ordinary Euclidean copies cost at most their literal finite cardinality
in union volume. -/
theorem volume_indexedEuclideanTranslatedShadingUnion_le_card_mul
    {tau : Type u} {kappa : Type v}
    [Fintype tau]
    (shift : tau -> Space) (F : ConvexFamily kappa) (Y : Shading F) :
    volume (indexedEuclideanTranslatedShading shift F Y).shadedUnion <=
      (Fintype.card tau : ENNReal) * volume Y.shadedUnion := by
  rw [indexedEuclideanTranslatedShading_shadedUnion]
  calc
    volume (⋃ j : tau, (fun x => shift j + x) '' Y.shadedUnion) <=
        ∑ j : tau, volume ((fun x => shift j + x) '' Y.shadedUnion) :=
      measure_iUnion_fintype_le volume _
    _ = ∑ _j : tau, volume Y.shadedUnion := by
      apply Finset.sum_congr rfl
      intro j _hj
      exact volume_euclideanTranslate_image (shift j) Y.shadedUnion
    _ = (Fintype.card tau : ENNReal) * volume Y.shadedUnion := by
      simp [nsmul_eq_mul]

/-- Safe division form of the Euclidean finite-copy loss. -/
theorem lower_div_card_le_volume_originalShadedUnion
    {tau : Type u} {kappa : Type v}
    [Fintype tau]
    (shift : tau -> Space) (F : ConvexFamily kappa) (Y : Shading F)
    (lower : ENNReal)
    (hlower : lower <=
      volume (indexedEuclideanTranslatedShading shift F Y).shadedUnion) :
    lower / (Fintype.card tau : ENNReal) <= volume Y.shadedUnion := by
  apply ENNReal.div_le_of_le_mul'
  exact hlower.trans
    (volume_indexedEuclideanTranslatedShadingUnion_le_card_mul shift F Y)

/-! ## The actual hierarchy terminal output -/

variable {depth : Nat} {nominalRadius : Nat -> NNReal}
  {Index : Nat -> Type*}
  [forall l, Fintype (Index l)] [forall l, DecidableEq (Index l)]
  {H : MultiscaleTubeHierarchy depth nominalRadius Index}
  {G : HierarchyRandomMotionGeometry H}

/-- The active level-zero source family whose product with terminal paths is
the hierarchy output index.  The restriction retains each active occurrence. -/
def terminalSourceTubeFamily :
    UniformTubeFamily (H.effectiveRadius 0)
      {i // i ∈ (H.family 0).refinement.refined} :=
  (H.effectiveFamily 0).restrictTo (H.family 0).refinement.refined

@[simp]
theorem terminalSourceTubeFamily_tubes
    (i : {i // i ∈ (H.family 0).refinement.refined}) :
    (terminalSourceTubeFamily (H := H)).tubes i =
      (H.effectiveFamily 0).tubes i.1 :=
  rfl

/-- Restrict any shading on the full effective family to the active terminal
source subtype. -/
def terminalSourceShading
    (Y : Shading (H.effectiveFamily 0).bodyFamily) :
    Shading (terminalSourceTubeFamily (H := H)).bodyFamily where
  carrier i := Y.carrier i.1
  measurable_carrier i := Y.measurable_carrier i.1
  carrier_subset i := Y.carrier_subset i.1

variable (C : HierarchyJointRandomMotionCertificate H G)

/-- The terminal tube body family is exactly the generic product-indexed
Euclidean translate family. -/
theorem terminalTubeBodyFamily_eq_indexedEuclideanTranslatedBodyFamily :
    (terminalTubeFamily C).bodyFamily =
      indexedEuclideanTranslatedBodyFamily
        (fun path : C.Path => C.output.toComposition.composedVector path)
        (terminalSourceTubeFamily (H := H)).bodyFamily := by
  funext a
  exact translateTube_body_eq_translateConvexBody
    ((H.effectiveFamily 0).tubes a.2.1)
    (C.output.toComposition.composedVector a.1)

/-- The generic product construction, transported only across the proved
body-family equality, is a genuine shading of the actual terminal tubes. -/
def terminalTranslatedShading
    (Y : Shading (terminalSourceTubeFamily (H := H)).bodyFamily) :
    Shading (terminalTubeFamily C).bodyFamily where
  carrier a :=
    (fun x => C.output.toComposition.composedVector a.1 + x) '' Y.carrier a.2
  measurable_carrier a :=
    (MeasurableEquiv.addLeft
      (C.output.toComposition.composedVector a.1)).measurableSet_image.mpr
        (Y.measurable_carrier a.2)
  carrier_subset a := by
    change
      (fun x => C.output.toComposition.composedVector a.1 + x) ''
          Y.carrier a.2 ⊆
        ((translateTube ((H.effectiveFamily 0).tubes a.2.1)
          (C.output.toComposition.composedVector a.1)).body : Set Space)
    rw [translateTube_coe_body]
    apply Set.image_mono
    simpa only [UniformTubeFamily.bodyFamily_apply,
      terminalSourceTubeFamily_tubes, Tube.coe_body] using
        Y.carrier_subset a.2

@[simp]
theorem terminalTranslatedShading_carrier
    (Y : Shading (terminalSourceTubeFamily (H := H)).bodyFamily)
    (a : C.FinalIndex) :
    (terminalTranslatedShading C Y).carrier a =
      (fun x => C.output.toComposition.composedVector a.1 + x) ''
        Y.carrier a.2 := by
  rfl

/-- Each translated shaded piece lies in the carrier of the literal final
tube selected by the hierarchy certificate. -/
theorem terminalTranslatedShading_carrier_subset_finalTube
    (Y : Shading (terminalSourceTubeFamily (H := H)).bodyFamily)
    (a : C.FinalIndex) :
    (terminalTranslatedShading C Y).carrier a ⊆
      (C.finalTube a).carrier := by
  simpa only [UniformTubeFamily.bodyFamily_apply, terminalTubeFamily_tubes,
    Tube.coe_body] using
    (terminalTranslatedShading C Y).carrier_subset a

/-- Terminal shading mass is the path count times active source mass. -/
theorem terminalTranslatedShading_shadingMass
    (Y : Shading (terminalSourceTubeFamily (H := H)).bodyFamily) :
    (terminalTranslatedShading C Y).shadingMass =
      (Fintype.card C.Path : ENNReal) * Y.shadingMass := by
  classical
  unfold Shading.shadingMass
  rw [Fintype.sum_prod_type]
  simp_rw [terminalTranslatedShading_carrier,
    volume_euclideanTranslate_image]
  simp [nsmul_eq_mul]

theorem terminalTubeFamily_familyVolume :
    familyVolume (terminalTubeFamily C).bodyFamily =
      (Fintype.card C.Path : ENNReal) *
        familyVolume (terminalSourceTubeFamily (H := H)).bodyFamily := by
  rw [terminalTubeBodyFamily_eq_indexedEuclideanTranslatedBodyFamily C]
  exact indexedEuclideanTranslatedBodyFamily_familyVolume
    (fun path : C.Path => C.output.toComposition.composedVector path)
    (terminalSourceTubeFamily (H := H)).bodyFamily

/-- The certificate supplies a nonempty path type, so terminal translation
preserves the active source shading density exactly. -/
theorem terminalTranslatedShading_shadingDensity
    (Y : Shading (terminalSourceTubeFamily (H := H)).bodyFamily) :
    (terminalTranslatedShading C Y).shadingDensity = Y.shadingDensity := by
  let _ : Nonempty C.Path := C.path_nonempty
  unfold Shading.shadingDensity
  rw [terminalTranslatedShading_shadingMass,
    terminalTubeFamily_familyVolume]
  apply ENNReal.mul_div_mul_left
  · exact_mod_cast
      (Fintype.card_pos_iff.mpr (inferInstance : Nonempty C.Path)).ne'
  · exact ENNReal.coe_ne_top

/-- Exact terminal union covariance for ordinary Euclidean hierarchy
translations. -/
theorem terminalTranslatedShading_shadedUnion
    (Y : Shading (terminalSourceTubeFamily (H := H)).bodyFamily) :
    (terminalTranslatedShading C Y).shadedUnion =
      ⋃ path : C.Path,
        (fun x => C.output.toComposition.composedVector path + x) ''
          Y.shadedUnion := by
  exact indexedEuclideanTranslatedShading_shadedUnion
    (fun path : C.Path => C.output.toComposition.composedVector path)
    (terminalSourceTubeFamily (H := H)).bodyFamily Y

/-- The hierarchy terminal union returns to the active source union with
exactly the literal path-cardinality loss. -/
theorem volume_terminalTranslatedShading_le_pathCard_mul
    (Y : Shading (terminalSourceTubeFamily (H := H)).bodyFamily) :
    volume (terminalTranslatedShading C Y).shadedUnion <=
      (Fintype.card C.Path : ENNReal) * volume Y.shadedUnion := by
  exact volume_indexedEuclideanTranslatedShadingUnion_le_card_mul
    (fun path : C.Path => C.output.toComposition.composedVector path)
    (terminalSourceTubeFamily (H := H)).bodyFamily Y

theorem lower_div_pathCard_le_volume_terminalSourceShadedUnion
    (Y : Shading (terminalSourceTubeFamily (H := H)).bodyFamily)
    (lower : ENNReal)
    (hlower : lower <= volume (terminalTranslatedShading C Y).shadedUnion) :
    lower / (Fintype.card C.Path : ENNReal) <= volume Y.shadedUnion := by
  apply ENNReal.div_le_of_le_mul'
  exact hlower.trans (volume_terminalTranslatedShading_le_pathCard_mul C Y)

theorem terminalSource_averageMultiplicity_le_of_shadingMass_le_factor_mul_copyAverage
    (Y : Shading (terminalSourceTubeFamily (H := H)).bodyFamily)
    (factor : ENNReal)
    (hmass : Y.shadingMass <= factor *
      (volume (terminalTranslatedShading C Y).shadedUnion /
        (Fintype.card C.Path : ENNReal))) :
    Y.averageMultiplicity <= factor := by
  have hcopyAverage :
      volume (terminalTranslatedShading C Y).shadedUnion /
          (Fintype.card C.Path : ENNReal) <= volume Y.shadedUnion :=
    lower_div_pathCard_le_volume_terminalSourceShadedUnion C Y _ le_rfl
  unfold Shading.averageMultiplicity
  apply ENNReal.div_le_of_le_mul
  exact hmass.trans (mul_le_mul' le_rfl hcopyAverage)

#print axioms indexedEuclideanTranslatedShading
#print axioms indexedEuclideanTranslatedShading_shadingMass
#print axioms indexedEuclideanTranslatedShading_shadingDensity
#print axioms indexedEuclideanTranslatedShading_shadedUnion
#print axioms volume_indexedEuclideanTranslatedShadingUnion_le_card_mul
#print axioms terminalTubeBodyFamily_eq_indexedEuclideanTranslatedBodyFamily
#print axioms terminalTranslatedShading
#print axioms terminalTranslatedShading_shadingMass
#print axioms terminalTubeFamily_familyVolume
#print axioms terminalTranslatedShading_shadingDensity
#print axioms terminalTranslatedShading_shadedUnion
#print axioms volume_terminalTranslatedShading_le_pathCard_mul
#print axioms lower_div_pathCard_le_volume_terminalSourceShadedUnion
#print axioms terminalSource_averageMultiplicity_le_of_shadingMass_le_factor_mul_copyAverage

end

end FamilyStickyHierarchyEuclideanTranslatedShadingBridgeV1
