import FamilyStickyGrounding.FamilyStickyWZ2TranslatedShadingUnionCovarianceV1
import FamilyStickyGrounding.FamilyStickyWZ2TwistedFiberVolumeV1

set_option autoImplicit false

open MeasureTheory

namespace FamilyStickyWZ2AmbientCinematicTranslationVolumeV1

open FamilyStickyWZ2CinematicTranslationV1
open FamilyStickyWZ2ProjectionSliceRetentionV1
open FamilyStickyWZ2TranslatedShadingUnionCovarianceV1
open FamilyStickyWZ2TwistedFiberVolumeV1
open LeanEval.Analysis.WangZahlKakeya

noncomputable section

/-!
# Ambient volume of the WZ2 parameter translation

The ambient parameter transport is a triangular affine shear with determinant
one.  This module derives its three-dimensional volume preservation from the
tracked product-coordinate measure equivalence and the already-proved planar
cinematic translation.  No density statement is supplied as a premise.
-/

private abbrev realVolume : Measure Real := volume

/-- Product-coordinate presentation of the ambient parameter translation. -/
def ambientCoordinateTranslation
    (a0 b0 d0 : Real) (q : Real × (Real × Real)) :
    Real × (Real × Real) :=
  (q.1 + a0, cinematicTranslation (fun _ => 1) b0 0 d0 q.2)

/-- The product-coordinate translation preserves three-dimensional product
Lebesgue measure. -/
theorem ambientCoordinateTranslation_measurePreserving
    (a0 b0 d0 : Real) :
    MeasurePreserving (ambientCoordinateTranslation a0 b0 d0)
      (realVolume.prod (realVolume.prod realVolume))
      (realVolume.prod (realVolume.prod realVolume)) := by
  have hx : MeasurePreserving (fun x : Real => x + a0)
      realVolume realVolume :=
    measurePreserving_add_right realVolume a0
  have hyz : MeasurePreserving
      (cinematicTranslation (fun _ : Real => 1) b0 0 d0)
      (realVolume.prod realVolume) (realVolume.prod realVolume) :=
    cinematicTranslation_measurePreserving
      (fun _ : Real => 1) measurable_const b0 0 d0
  change MeasurePreserving
    (Prod.map (fun x : Real => x + a0)
      (cinematicTranslation (fun _ : Real => 1) b0 0 d0))
      (realVolume.prod (realVolume.prod realVolume))
      (realVolume.prod (realVolume.prod realVolume))
  exact hx.prod hyz

/-- The explicit ambient shear is the product-coordinate map conjugated by
the tracked Euclidean/product-coordinate equivalence. -/
theorem ambientCinematicTranslation_eq_coordinates
    (a0 b0 d0 : Real) :
    ambientCinematicTranslation a0 b0 d0 =
      coordinatesToSpace ∘ ambientCoordinateTranslation a0 b0 d0 ∘
        spaceCoordinates := by
  funext p
  ext i
  fin_cases i <;>
    simp [ambientCinematicTranslation, ambientCoordinateTranslation,
      cinematicTranslation, cinematicShift, coordinatesToSpace,
      spaceCoordinates, point3, Function.comp_def]; ring

/-- The ambient WZ2 parameter translation preserves Euclidean volume. -/
theorem ambientCinematicTranslation_measurePreserving
    (a0 b0 d0 : Real) :
    MeasurePreserving (ambientCinematicTranslation a0 b0 d0)
      (volume : Measure Space) volume := by
  have h := coordinatesToSpace_measurePreserving.comp
    ((ambientCoordinateTranslation_measurePreserving a0 b0 d0).comp
      spaceCoordinates_measurePreserving)
  rw [ambientCinematicTranslation_eq_coordinates]
  exact h

/-- Negating all three translation parameters gives a left inverse. -/
theorem ambientCinematicTranslation_neg_left
    (a0 b0 d0 : Real) (p : Space) :
    ambientCinematicTranslation (-a0) (-b0) (-d0)
        (ambientCinematicTranslation a0 b0 d0 p) = p := by
  ext i
  fin_cases i <;>
    simp [ambientCinematicTranslation, point3];
    ring

/-- Negating all three translation parameters gives a right inverse. -/
theorem ambientCinematicTranslation_neg_right
    (a0 b0 d0 : Real) (p : Space) :
    ambientCinematicTranslation a0 b0 d0
        (ambientCinematicTranslation (-a0) (-b0) (-d0) p) = p := by
  simpa only [neg_neg] using
    ambientCinematicTranslation_neg_left (-a0) (-b0) (-d0) p

/-- Ambient parameter translation as a measurable equivalence. -/
def ambientCinematicTranslationMeasurableEquiv
    (a0 b0 d0 : Real) : Space ≃ᵐ Space where
  toFun := ambientCinematicTranslation a0 b0 d0
  invFun := ambientCinematicTranslation (-a0) (-b0) (-d0)
  left_inv := ambientCinematicTranslation_neg_left a0 b0 d0
  right_inv := ambientCinematicTranslation_neg_right a0 b0 d0
  measurable_toFun :=
    (ambientCinematicTranslation_measurePreserving a0 b0 d0).measurable
  measurable_invFun :=
    (ambientCinematicTranslation_measurePreserving
      (-a0) (-b0) (-d0)).measurable

/-- The ambient parameter translation preserves the volume of every image
set, without a measurability assumption on that set. -/
theorem volume_ambientCinematicTranslation_image
    (a0 b0 d0 : Real) (X : Set Space) :
    volume (ambientCinematicTranslation a0 b0 d0 '' X) = volume X := by
  have h :=
    (ambientCinematicTranslation_measurePreserving a0 b0 d0).measure_preimage_emb
      (ambientCinematicTranslationMeasurableEquiv
        a0 b0 d0).measurableEmbedding
      (ambientCinematicTranslation a0 b0 d0 '' X)
  have hinjective : Function.Injective
      (ambientCinematicTranslation a0 b0 d0) :=
    (ambientCinematicTranslationMeasurableEquiv a0 b0 d0).injective
  rw [Set.preimage_image_eq _ hinjective] at h
  exact h.symm

/-- Every translated shading carrier therefore retains its ambient volume. -/
theorem volume_translatedShadingCarrier
    {kappa : Type*} (a0 b0 d0 : Real)
    (Y : kappa -> Set Space) (i : kappa) :
    volume (translatedShadingCarrier a0 b0 d0 Y i) =
      volume (Y i) := by
  exact volume_ambientCinematicTranslation_image a0 b0 d0 (Y i)

#print axioms ambientCoordinateTranslation_measurePreserving
#print axioms ambientCinematicTranslation_eq_coordinates
#print axioms ambientCinematicTranslation_measurePreserving
#print axioms ambientCinematicTranslation_neg_left
#print axioms ambientCinematicTranslation_neg_right
#print axioms volume_ambientCinematicTranslation_image
#print axioms volume_translatedShadingCarrier

end
end FamilyStickyWZ2AmbientCinematicTranslationVolumeV1
