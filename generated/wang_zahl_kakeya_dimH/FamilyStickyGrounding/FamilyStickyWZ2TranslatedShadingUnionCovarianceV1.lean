import FamilyStickyGrounding.FamilyStickyWZ2CinematicTranslationV1

set_option autoImplicit false

open MeasureTheory

namespace FamilyStickyWZ2TranslatedShadingUnionCovarianceV1

open FamilyStickyWZ2ProjectionSliceRetentionV1
open FamilyStickyWZ2CinematicTranslationV1
open LeanEval.Analysis.WangZahlKakeya

noncomputable section

/-!
# Covariance of translated WZ2 shading unions

WZ2 transports a shading from parameters `(a,b,d)` to
`(a+a0,b+b0,d+d0)` at fixed `c`.  The ambient map below is that literal
transport.  It commutes pointwise with the twisted projection and the
cinematic translation, so covariance and planar-volume invariance of an
arbitrary indexed union follow without either conclusion as a premise.

This module does not construct the earlier refinement of the tube family or
assert the later cinematic `L^(3/2)` estimate.
-/

/-- Ambient transport implementing the WZ2 parameter translation
`(a,b,d) -> (a+a0,b+b0,d+d0)` at every height. -/
def ambientCinematicTranslation
    (a0 b0 d0 : Real) (p : Space) : Space :=
  point3 (p 0 + a0) (p 1 + b0 + d0 * p 2) (p 2)

/-- The ambient transport sends each parameter-line point to the point with
the translated reduced parameters at the same height. -/
theorem ambientCinematicTranslation_parameterLinePoint
    (a b c d a0 b0 d0 t : Real) :
    ambientCinematicTranslation a0 b0 d0
        (parameterLinePoint a b c d t) =
      parameterLinePoint (a + a0) (b + b0) c (d + d0) t := by
  ext i
  fin_cases i <;>
    simp [ambientCinematicTranslation, parameterLinePoint, point3] <;>
    ring

/-- Ambient parameter transport and planar cinematic translation commute
exactly through the twisted projection. -/
theorem twistedProjection_ambientCinematicTranslation
    (f : Real -> Real) (a0 b0 d0 : Real) (p : Space) :
    twistedProjection f (ambientCinematicTranslation a0 b0 d0 p) =
      cinematicTranslation f a0 b0 d0 (twistedProjection f p) := by
  apply Prod.ext
  · simp [twistedProjection, ambientCinematicTranslation, point3,
      cinematicTranslation, cinematicShift]
    ring
  · simp [twistedProjection, ambientCinematicTranslation, point3,
      cinematicTranslation]

/-- Literal transport of one member of an indexed family of shading sets. -/
def translatedShadingCarrier
    {kappa : Type*} (a0 b0 d0 : Real)
    (Y : kappa -> Set Space) (i : kappa) : Set Space :=
  ambientCinematicTranslation a0 b0 d0 '' Y i

/-- The projected image of one transported shading set is exactly the
cinematic translation of its original projected image. -/
theorem twistedProjection_image_translatedShadingCarrier
    {kappa : Type*} (f : Real -> Real) (a0 b0 d0 : Real)
    (Y : kappa -> Set Space) (i : kappa) :
    twistedProjection f '' translatedShadingCarrier a0 b0 d0 Y i =
      cinematicTranslation f a0 b0 d0 ''
        (twistedProjection f '' Y i) := by
  ext q
  constructor
  · rintro ⟨p, ⟨r, hr, rfl⟩, rfl⟩
    refine ⟨twistedProjection f r, ⟨r, hr, rfl⟩, ?_⟩
    exact Eq.symm (twistedProjection_ambientCinematicTranslation f a0 b0 d0 r)
  · rintro ⟨q, ⟨p, hp, rfl⟩, rfl⟩
    refine ⟨ambientCinematicTranslation a0 b0 d0 p,
      ⟨p, hp, rfl⟩, ?_⟩
    exact twistedProjection_ambientCinematicTranslation
      f a0 b0 d0 p

/-- Exact set-level covariance for the union of an arbitrary indexed family
of transported shading sets. -/
theorem twistedProjection_iUnion_translatedShadingCarrier
    {kappa : Type*} (f : Real -> Real) (a0 b0 d0 : Real)
    (Y : kappa -> Set Space) :
    (⋃ i, twistedProjection f ''
        translatedShadingCarrier a0 b0 d0 Y i) =
      cinematicTranslation f a0 b0 d0 ''
        (⋃ i, twistedProjection f '' Y i) := by
  ext q
  constructor
  · intro hq
    rcases Set.mem_iUnion.mp hq with ⟨i, hi⟩
    rw [twistedProjection_image_translatedShadingCarrier] at hi
    rcases hi with ⟨r, hr, rfl⟩
    exact ⟨r, Set.mem_iUnion.mpr ⟨i, hr⟩, rfl⟩
  · rintro ⟨r, hr, rfl⟩
    rcases Set.mem_iUnion.mp hr with ⟨i, hi⟩
    apply Set.mem_iUnion.mpr
    refine ⟨i, ?_⟩
    rw [twistedProjection_image_translatedShadingCarrier]
    exact ⟨r, hi, rfl⟩

/-- The translated projected shading union has exactly the same planar
Lebesgue measure as the original union.  This is the formal content of the
translation covariance used in WZ2 equation `eq: translate`. -/
theorem volume_twistedProjection_iUnion_translatedShadingCarrier
    {kappa : Type*} (f : Real -> Real) (hf : Measurable f)
    (a0 b0 d0 : Real) (Y : kappa -> Set Space) :
    volume
        (⋃ i, twistedProjection f ''
          translatedShadingCarrier a0 b0 d0 Y i) =
      volume (⋃ i, twistedProjection f '' Y i) := by
  rw [twistedProjection_iUnion_translatedShadingCarrier]
  exact volume_cinematicTranslation_image f hf a0 b0 d0
    (⋃ i, twistedProjection f '' Y i)

#print axioms ambientCinematicTranslation_parameterLinePoint
#print axioms twistedProjection_ambientCinematicTranslation
#print axioms twistedProjection_image_translatedShadingCarrier
#print axioms twistedProjection_iUnion_translatedShadingCarrier
#print axioms volume_twistedProjection_iUnion_translatedShadingCarrier

end
end FamilyStickyWZ2TranslatedShadingUnionCovarianceV1
