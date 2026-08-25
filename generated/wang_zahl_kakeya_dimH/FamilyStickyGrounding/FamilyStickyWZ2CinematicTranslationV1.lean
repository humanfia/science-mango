import FamilyStickyGrounding.FamilyStickyWZ2ProjectionSliceRetentionV1

set_option autoImplicit false

open MeasureTheory

namespace FamilyStickyWZ2CinematicTranslationV1

open FamilyStickyWZ2ProjectionSliceRetentionV1
open LeanEval.Analysis.WangZahlKakeya

noncomputable section

/-!
# Cinematic parameter translations in WZ2 Section 7

This module formalizes the exact translation mechanism behind equations
`equivalenceOfUnions` and `eq: translate` in the WZ2 proof.  Translating the
reduced line parameters `(a,b,d)` produces a height-dependent horizontal
translation of the twisted projection.  The latter is proved area-preserving
as a triangular measurable skew product.

No cinematic-function estimate or projected-area lower bound is assumed.
-/

private abbrev realVolume : Measure Real := volume

/-- Horizontal displacement caused by translating `(a,b,d)` by
`(a0,b0,d0)`. -/
def cinematicShift (f : Real -> Real) (a0 b0 d0 z : Real) : Real :=
  a0 + b0 * f z + d0 * f z * z

/-- The corresponding height-dependent horizontal translation in the
twisted-projection plane. -/
def cinematicTranslation
    (f : Real -> Real) (a0 b0 d0 : Real) (q : ProjectionSpace) :
    ProjectionSpace :=
  (q.1 + cinematicShift f a0 b0 d0 q.2, q.2)

/-- Explicit inverse of `cinematicTranslation`. -/
def cinematicTranslationInverse
    (f : Real -> Real) (a0 b0 d0 : Real) (q : ProjectionSpace) :
    ProjectionSpace :=
  (q.1 - cinematicShift f a0 b0 d0 q.2, q.2)

theorem cinematicTranslationInverse_cinematicTranslation
    (f : Real -> Real) (a0 b0 d0 : Real) (q : ProjectionSpace) :
    cinematicTranslationInverse f a0 b0 d0
      (cinematicTranslation f a0 b0 d0 q) = q := by
  apply Prod.ext <;>
    simp [cinematicTranslationInverse, cinematicTranslation]

theorem cinematicTranslation_cinematicTranslationInverse
    (f : Real -> Real) (a0 b0 d0 : Real) (q : ProjectionSpace) :
    cinematicTranslation f a0 b0 d0
      (cinematicTranslationInverse f a0 b0 d0 q) = q := by
  apply Prod.ext <;>
    simp [cinematicTranslationInverse, cinematicTranslation]

/-- The same triangular map with height placed before the horizontal
coordinate. -/
private def cinematicTranslationBaseFirst
    (f : Real -> Real) (a0 b0 d0 : Real) (q : Real × Real) :
    Real × Real :=
  (q.1, q.2 + cinematicShift f a0 b0 d0 q.1)

/-- A measurable cinematic translation preserves planar Lebesgue measure. -/
theorem cinematicTranslation_measurePreserving
    (f : Real -> Real) (hf : Measurable f) (a0 b0 d0 : Real) :
    MeasurePreserving (cinematicTranslation f a0 b0 d0)
      (volume : Measure ProjectionSpace) volume := by
  have hbase :
      MeasurePreserving (cinematicTranslationBaseFirst f a0 b0 d0)
        (realVolume.prod realVolume) (realVolume.prod realVolume) := by
    refine MeasurePreserving.skew_product
      (g := fun z u => u + cinematicShift f a0 b0 d0 z)
      (MeasurePreserving.id realVolume) ?_ ?_
    · unfold cinematicShift
      fun_prop
    · filter_upwards with z
      exact
        (measurePreserving_add_right realVolume
          (cinematicShift f a0 b0 d0 z)).map_eq
  have hswap :
      MeasurePreserving (Prod.swap : Real × Real -> Real × Real)
        (realVolume.prod realVolume) (realVolume.prod realVolume) :=
    Measure.measurePreserving_swap
  have hproduct :
      MeasurePreserving (cinematicTranslation f a0 b0 d0)
        (realVolume.prod realVolume) (realVolume.prod realVolume) := by
    have h := hswap.comp (hbase.comp hswap)
    convert h using 1
    ext q <;> rfl
  simpa only [Measure.volume_eq_prod] using hproduct

/-- Cinematic translation as a measurable equivalence. -/
def cinematicTranslationMeasurableEquiv
    (f : Real -> Real) (hf : Measurable f) (a0 b0 d0 : Real) :
    ProjectionSpace ≃ᵐ ProjectionSpace where
  toFun := cinematicTranslation f a0 b0 d0
  invFun := cinematicTranslationInverse f a0 b0 d0
  left_inv := cinematicTranslationInverse_cinematicTranslation f a0 b0 d0
  right_inv := cinematicTranslation_cinematicTranslationInverse f a0 b0 d0
  measurable_toFun :=
    (cinematicTranslation_measurePreserving f hf a0 b0 d0).measurable
  measurable_invFun := by
    change Measurable (cinematicTranslationInverse f a0 b0 d0)
    unfold cinematicTranslationInverse cinematicShift
    fun_prop

/-- Cinematic translations preserve the area of the image of every set. -/
theorem volume_cinematicTranslation_image
    (f : Real -> Real) (hf : Measurable f) (a0 b0 d0 : Real)
    (X : Set ProjectionSpace) :
    volume (cinematicTranslation f a0 b0 d0 '' X) = volume X := by
  have h :=
    (cinematicTranslation_measurePreserving f hf a0 b0 d0).measure_preimage_emb
      (cinematicTranslationMeasurableEquiv f hf a0 b0 d0).measurableEmbedding
      (cinematicTranslation f a0 b0 d0 '' X)
  have hinjective : Function.Injective
      (cinematicTranslation f a0 b0 d0) := by
    intro q r hqr
    have := congrArg (cinematicTranslationInverse f a0 b0 d0) hqr
    simpa only [cinematicTranslationInverse_cinematicTranslation] using this
  rw [Set.preimage_image_eq _ hinjective] at h
  exact h.symm

/-- Translating `(a,b,d)` has exactly the displacement asserted in WZ2
Section 7, pointwise along the cinematic curve. -/
theorem cinematicTranslation_cinematicCurvePoint
    (f : Real -> Real) (a b c d a0 b0 d0 t : Real) :
    cinematicTranslation f a0 b0 d0
        (cinematicCurvePoint f a b c d t) =
      cinematicCurvePoint f (a + a0) (b + b0) c (d + d0) t := by
  apply Prod.ext
  · simp only [cinematicTranslation, cinematicShift, cinematicCurvePoint]
    ring
  · rfl

/-- The reduced parameter triple `(a,b,d)` at fixed `c`. -/
abbrev ReducedLineParameter := Real × (Real × Real)

/-- Translation of a reduced line parameter. -/
def translateReducedLineParameter
    (a0 b0 d0 : Real) (p : ReducedLineParameter) :
    ReducedLineParameter :=
  (p.1 + a0, (p.2.1 + b0, p.2.2 + d0))

/-- Union of the cinematic traces indexed by a set of reduced parameters. -/
def cinematicTraceFamily
    (f : Real -> Real) (c : Real) (parameters : Set ReducedLineParameter) :
    Set ProjectionSpace :=
  {q | exists p, p ∈ parameters ∧ exists t,
    q = cinematicCurvePoint f p.1 p.2.1 c p.2.2 t}

/-- Translating all reduced line parameters translates their entire union of
cinematic traces by the corresponding triangular map. -/
theorem cinematicTranslation_image_cinematicTraceFamily
    (f : Real -> Real) (c a0 b0 d0 : Real)
    (parameters : Set ReducedLineParameter) :
    cinematicTranslation f a0 b0 d0 ''
        cinematicTraceFamily f c parameters =
      cinematicTraceFamily f c
        (translateReducedLineParameter a0 b0 d0 '' parameters) := by
  ext q
  constructor
  · rintro ⟨r, ⟨p, hp, t, rfl⟩, rfl⟩
    refine ⟨translateReducedLineParameter a0 b0 d0 p, ⟨p, hp, rfl⟩, t, ?_⟩
    exact cinematicTranslation_cinematicCurvePoint
      f p.1 p.2.1 c p.2.2 a0 b0 d0 t
  · rintro ⟨p', ⟨p, hp, rfl⟩, t, rfl⟩
    refine ⟨cinematicCurvePoint f p.1 p.2.1 c p.2.2 t,
      ⟨p, hp, t, rfl⟩, ?_⟩
    exact cinematicTranslation_cinematicCurvePoint
      f p.1 p.2.1 c p.2.2 a0 b0 d0 t

/-- Exact area invariance of the translated union of cinematic traces,
formalizing the measure content of WZ2 equation `eq: translate`. -/
theorem volume_cinematicTraceFamily_translate
    (f : Real -> Real) (hf : Measurable f) (c a0 b0 d0 : Real)
    (parameters : Set ReducedLineParameter) :
    volume
        (cinematicTraceFamily f c
          (translateReducedLineParameter a0 b0 d0 '' parameters)) =
      volume (cinematicTraceFamily f c parameters) := by
  rw [← cinematicTranslation_image_cinematicTraceFamily]
  exact volume_cinematicTranslation_image f hf a0 b0 d0
    (cinematicTraceFamily f c parameters)

#print axioms cinematicTranslationInverse_cinematicTranslation
#print axioms cinematicTranslation_cinematicTranslationInverse
#print axioms cinematicTranslation_measurePreserving
#print axioms volume_cinematicTranslation_image
#print axioms cinematicTranslation_cinematicCurvePoint
#print axioms cinematicTranslation_image_cinematicTraceFamily
#print axioms volume_cinematicTraceFamily_translate

end

end FamilyStickyWZ2CinematicTranslationV1
