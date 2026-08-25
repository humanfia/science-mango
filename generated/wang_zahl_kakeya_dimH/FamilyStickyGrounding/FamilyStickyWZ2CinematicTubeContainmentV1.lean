import FamilyStickyGrounding.FamilyStickyWZ2CinematicTranslationV1

set_option autoImplicit false

namespace FamilyStickyWZ2CinematicTubeContainmentV1

open FamilyStickyWZ2ProjectionSliceRetentionV1
open LeanEval.Analysis.WangZahlKakeya

noncomputable section

/-!
# Coordinate tube containment in a thickened cinematic trace

This module proves the elementary geometric producer used before the WZ2
cinematic estimate: a coordinatewise thickening of the line
`(a + ct, b + dt, t)` projects into an explicitly thickened neighborhood of
its cinematic curve.  The proof exposes the exact three-term projection
error and only uses pointwise boundedness/Lipschitz hypotheses on `f`.
-/

/-- A coordinatewise `delta`-thickening of one parametrized line, restricted
to heights in `I`. -/
def coordinateLineTube
    (I : Set Real) (a b c d delta : Real) : Set Space :=
  {p | exists t, t ∈ I ∧
    |p 0 - (a + c * t)| <= delta ∧
    |p 1 - (b + d * t)| <= delta ∧
    |p 2 - t| <= delta}

/-- Coordinatewise `R`-neighborhood of a cinematic trace. -/
def cinematicBoxNeighborhood
    (f : Real -> Real) (I : Set Real)
    (a b c d R : Real) : Set ProjectionSpace :=
  {q | exists t, t ∈ I ∧
    |q.1 - (cinematicCurvePoint f a b c d t).1| <= R ∧
    |q.2 - (cinematicCurvePoint f a b c d t).2| <= R}

/-- Exact decomposition of the horizontal projection error into the ambient
`x` error, the amplified `y` error, and variation of the slope function. -/
theorem twistedProjection_cinematicCurve_first_error
    (f : Real -> Real) (p : Space) (a b c d t : Real) :
    (twistedProjection f p).1 -
        (cinematicCurvePoint f a b c d t).1 =
      (p 0 - (a + c * t)) +
        f (p 2) * (p 1 - (b + d * t)) +
          (f (p 2) - f t) * (b + d * t) := by
  simp only [twistedProjection, cinematicCurvePoint]
  ring

/-- The vertical projection error is exactly the height error. -/
theorem twistedProjection_cinematicCurve_second_error
    (f : Real -> Real) (p : Space) (a b c d t : Real) :
    (twistedProjection f p).2 -
        (cinematicCurvePoint f a b c d t).2 = p 2 - t := by
  rfl

/-- Quantitative horizontal error bound following from the exact
decomposition. -/
theorem abs_twistedProjection_cinematicCurve_first_le
    (f : Real -> Real) (p : Space) (a b c d t delta F L B : Real)
    (hdelta : 0 <= delta) (hF : 0 <= F) (hL : 0 <= L) (_hB : 0 <= B)
    (hx : |p 0 - (a + c * t)| <= delta)
    (hy : |p 1 - (b + d * t)| <= delta)
    (hz : |p 2 - t| <= delta)
    (hfBound : |f (p 2)| <= F)
    (hfLip : |f (p 2) - f t| <= L * |p 2 - t|)
    (hlineY : |b + d * t| <= B) :
    |(twistedProjection f p).1 -
        (cinematicCurvePoint f a b c d t).1| <=
      delta + F * delta + L * delta * B := by
  rw [twistedProjection_cinematicCurve_first_error]
  have hyTerm :
      |f (p 2) * (p 1 - (b + d * t))| <= F * delta := by
    rw [abs_mul]
    exact mul_le_mul hfBound hy (abs_nonneg _) hF
  have hfVariation : |f (p 2) - f t| <= L * delta := by
    exact hfLip.trans (mul_le_mul_of_nonneg_left hz hL)
  have hvariationTerm :
      |(f (p 2) - f t) * (b + d * t)| <= (L * delta) * B := by
    rw [abs_mul]
    exact mul_le_mul hfVariation hlineY (abs_nonneg _)
      (mul_nonneg hL hdelta)
  calc
    |(p 0 - (a + c * t)) +
        f (p 2) * (p 1 - (b + d * t)) +
          (f (p 2) - f t) * (b + d * t)| <=
        |p 0 - (a + c * t) +
          f (p 2) * (p 1 - (b + d * t))| +
            |(f (p 2) - f t) * (b + d * t)| := abs_add_le _ _
    _ <=
        (|p 0 - (a + c * t)| +
          |f (p 2) * (p 1 - (b + d * t))|) +
            |(f (p 2) - f t) * (b + d * t)| := by
      gcongr
      exact abs_add_le _ _
    _ <= delta + F * delta + (L * delta) * B := by
      exact add_le_add (add_le_add hx hyTerm) hvariationTerm

/-- A coordinate tube projects into the cinematic box neighborhood with the
explicit radius `delta + F*delta + L*delta*B`. -/
theorem twistedProjection_image_coordinateLineTube_subset
    (f : Real -> Real) (I : Set Real)
    (a b c d delta F L B : Real)
    (hdelta : 0 <= delta) (hF : 0 <= F) (hL : 0 <= L) (hB : 0 <= B)
    (hfBound : forall z, |f z| <= F)
    (hfLip : forall z t, |f z - f t| <= L * |z - t|)
    (hlineY : forall t, t ∈ I -> |b + d * t| <= B) :
    twistedProjection f '' coordinateLineTube I a b c d delta ⊆
      cinematicBoxNeighborhood f I a b c d
        (delta + F * delta + L * delta * B) := by
  rintro q ⟨p, hp, rfl⟩
  rcases hp with ⟨t, ht, hx, hy, hz⟩
  refine ⟨t, ht, ?_, ?_⟩
  · exact abs_twistedProjection_cinematicCurve_first_le
      f p a b c d t delta F L B hdelta hF hL hB
      hx hy hz (hfBound (p 2)) (hfLip (p 2) t) (hlineY t ht)
  · rw [twistedProjection_cinematicCurve_second_error]
    have hdeltaRadius :
        delta <= delta + F * delta + L * delta * B := by
      have hFdelta : 0 <= F * delta := mul_nonneg hF hdelta
      have hLdeltaB : 0 <= L * delta * B :=
        mul_nonneg (mul_nonneg hL hdelta) hB
      linarith
    exact hz.trans hdeltaRadius

/-- Any shaded subset of the coordinate tube obeys the same projected
containment. -/
theorem twistedProjection_image_subset_cinematicBoxNeighborhood
    (f : Real -> Real) (I : Set Real)
    (a b c d delta F L B : Real) (Y : Set Space)
    (hY : Y ⊆ coordinateLineTube I a b c d delta)
    (hdelta : 0 <= delta) (hF : 0 <= F) (hL : 0 <= L) (hB : 0 <= B)
    (hfBound : forall z, |f z| <= F)
    (hfLip : forall z t, |f z - f t| <= L * |z - t|)
    (hlineY : forall t, t ∈ I -> |b + d * t| <= B) :
    twistedProjection f '' Y ⊆
      cinematicBoxNeighborhood f I a b c d
        (delta + F * delta + L * delta * B) := by
  exact (Set.image_mono hY).trans
    (twistedProjection_image_coordinateLineTube_subset
      f I a b c d delta F L B hdelta hF hL hB
      hfBound hfLip hlineY)

#print axioms twistedProjection_cinematicCurve_first_error
#print axioms twistedProjection_cinematicCurve_second_error
#print axioms abs_twistedProjection_cinematicCurve_first_le
#print axioms twistedProjection_image_coordinateLineTube_subset
#print axioms twistedProjection_image_subset_cinematicBoxNeighborhood

end

end FamilyStickyWZ2CinematicTubeContainmentV1
