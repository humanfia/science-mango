import FamilyStickyGrounding.FamilyStickyWZ2ShadingPopularityV2
import Mathlib.MeasureTheory.Measure.Prod

set_option autoImplicit false

open scoped BigOperators ENNReal
open MeasureTheory

namespace FamilyStickyWZ2ProjectionSliceRetentionV1

open LeanEval.Analysis.WangZahlKakeya

noncomputable section

/-!
# WZ2 twisted-projection slices and level retention

This module isolates the first projection/slicing producer behind the
double-counting step in Section 7 (lines 1787--1790) of Wang--Zahl,
*The Assouad dimension of Kakeya sets in R3*.

It proves three independent facts:

* the twisted projection has an explicit fiber-coordinate equivalence;
* Tonelli identifies a projected slice multiplicity integral with the
  integral on the corresponding product pullback;
* a large subset of one multiplicity level retains a quantitative fraction
  of the full multiplicity integral.

The actual change-of-variables statement that the nonlinear fiber chart
preserves Euclidean volume is deliberately not asserted here.  In particular,
no restricted-multiplicity lower bound or conclusion of WZ2 Theorem 5.2 is
used as a premise.
-/

/-- The two coordinates of the twisted projection. -/
abbrev ProjectionSpace := Real × Real

/-- The WZ2 twisted projection `pi_f(x,y,z) = (x + f(z)y, z)`. -/
def twistedProjection (f : Real -> Real) (p : Space) : ProjectionSpace :=
  (p 0 + f (p 2) * p 1, p 2)

/-- A point of three-dimensional Euclidean space in coordinates. -/
def point3 (x y z : Real) : Space :=
  WithLp.toLp 2 ![x, y, z]

/-- The explicit fiber chart over the twisted projection: `(u,z)` is the
projected point and `y` is the fiber coordinate. -/
def twistedFiberChart (f : Real -> Real) (q : ProjectionSpace × Real) : Space :=
  point3 (q.1.1 - f q.1.2 * q.2) q.2 q.1.2

/-- Coordinates inverse to `twistedFiberChart`. -/
def twistedFiberCoordinates
    (f : Real -> Real) (p : Space) : ProjectionSpace × Real :=
  (twistedProjection f p, p 1)

/-- The chart lands on the requested twisted-projection fiber. -/
theorem twistedProjection_twistedFiberChart
    (f : Real -> Real) (q : ProjectionSpace × Real) :
    twistedProjection f (twistedFiberChart f q) = q.1 := by
  apply Prod.ext
  · simp [twistedProjection, twistedFiberChart, point3]
  · simp [twistedProjection, twistedFiberChart, point3]

/-- Fiber coordinates recover every point of ambient space. -/
theorem twistedFiberChart_twistedFiberCoordinates
    (f : Real -> Real) (p : Space) :
    twistedFiberChart f (twistedFiberCoordinates f p) = p := by
  ext i
  fin_cases i <;>
    simp [twistedFiberChart, twistedFiberCoordinates, twistedProjection, point3]

/-- Twisted fiber coordinates are an exact equivalence, before any measure
transport is invoked. -/
def twistedFiberEquiv (f : Real -> Real) :
    Space ≃ (ProjectionSpace × Real) where
  toFun := twistedFiberCoordinates f
  invFun := twistedFiberChart f
  left_inv := twistedFiberChart_twistedFiberCoordinates f
  right_inv := by
    intro q
    apply Prod.ext
    · exact twistedProjection_twistedFiberChart f q
    · simp [twistedFiberCoordinates, twistedFiberChart, point3]

/-- Parametrization of the affine line used in WZ2 Section 7. -/
def parameterLinePoint (a b c d t : Real) : Space :=
  point3 (a + c * t) (b + d * t) t

/-- The cinematic curve that is the twisted-projection image of the line. -/
def cinematicCurvePoint
    (f : Real -> Real) (a b c d t : Real) : ProjectionSpace :=
  (a + c * t + f t * (b + d * t), t)

/-- Exact pointwise form of WZ2 equation at lines 1797--1799. -/
theorem twistedProjection_parameterLinePoint
    (f : Real -> Real) (a b c d t : Real) :
    twistedProjection f (parameterLinePoint a b c d t) =
      cinematicCurvePoint f a b c d t := by
  rfl

/-- Pulling a target set back through the fiber chart gives the literal
product of that set with the full fiber. -/
theorem twistedFiberChart_preimage_twistedProjection_preimage
    (f : Real -> Real) (X : Set ProjectionSpace) :
    twistedFiberChart f ⁻¹' (twistedProjection f ⁻¹' X) =
      X ×ˢ (Set.univ : Set Real) := by
  ext q
  simp only [Set.mem_preimage, Set.mem_prod, Set.mem_univ, and_true]
  rw [twistedProjection_twistedFiberChart]

section ProductSlices

variable {alpha beta : Type*} [MeasurableSpace alpha] [MeasurableSpace beta]
variable (nu : Measure beta)

/-- Multiplicity on the target obtained by integrating a nonnegative
incidence function along each fiber. -/
def projectedSliceMultiplicity (g : alpha × beta -> ENNReal) (x : alpha) : ENNReal :=
  ∫⁻ y, g (x, y) ∂nu

/-- Tonelli on a restricted target set: projected slice mass is exactly the
mass of the product pullback. -/
theorem lintegral_projectedSliceMultiplicity_restrict
    [SFinite nu] (mu : Measure alpha) [SFinite mu]
    (g : alpha × beta -> ENNReal) (X : Set alpha)
    (hg : Measurable g) :
    (∫⁻ x in X, projectedSliceMultiplicity nu g x ∂mu) =
      ∫⁻ q in X ×ˢ (Set.univ : Set beta), g q ∂(mu.prod nu) := by
  symm
  simpa [projectedSliceMultiplicity] using
    (setLIntegral_prod (μ := mu) (ν := nu)
      (s := X) (t := (Set.univ : Set beta)) g hg.aemeasurable)

end ProductSlices

section LevelRetention

variable {omega : Type*} [MeasurableSpace omega]

/-- A subset retaining a `q`-fraction of the measure of one multiplicity
level retains a `q / C`-fraction of its multiplicity integral.  The
cross-multiplied ENNReal form avoids every finiteness or nonzero side
condition. -/
theorem levelSubset_retains_lintegral
    (mu : Measure omega) (multiplicity : omega -> ENNReal)
    (base kept : Set omega) (q C level : ENNReal)
    (hkeptMeasurable : MeasurableSet kept)
    (hbaseUpper : forall x, x ∈ base -> multiplicity x <= C * level)
    (hkeptLower : forall x, x ∈ kept -> level <= multiplicity x)
    (hmeasure : q * mu base <= mu kept) :
    q * (∫⁻ x in base, multiplicity x ∂mu) <=
      C * (∫⁻ x in kept, multiplicity x ∂mu) := by
  have hbaseIntegral :
      (∫⁻ x in base, multiplicity x ∂mu) <=
        (C * level) * mu base := by
    calc
      (∫⁻ x in base, multiplicity x ∂mu) <=
          ∫⁻ _x in base, C * level ∂mu := by
        exact setLIntegral_mono measurable_const hbaseUpper
      _ = (C * level) * mu base := setLIntegral_const base (C * level)
  have hkeptIntegral :
      level * mu kept <= ∫⁻ x in kept, multiplicity x ∂mu := by
    calc
      level * mu kept = ∫⁻ _x in kept, level ∂mu :=
        (setLIntegral_const kept level).symm
      _ <= ∫⁻ x in kept, multiplicity x ∂mu := by
        exact setLIntegral_mono' hkeptMeasurable hkeptLower
  calc
    q * (∫⁻ x in base, multiplicity x ∂mu) <=
        q * ((C * level) * mu base) := mul_le_mul' le_rfl hbaseIntegral
    _ = C * (level * (q * mu base)) := by ac_rfl
    _ <= C * (level * mu kept) := by
      exact mul_le_mul' le_rfl (mul_le_mul' le_rfl hmeasure)
    _ <= C * (∫⁻ x in kept, multiplicity x ∂mu) :=
      mul_le_mul' le_rfl hkeptIntegral

end LevelRetention

section ProductPullbackRetention

variable {alpha beta : Type*} [MeasurableSpace alpha] [MeasurableSpace beta]

/-- Combined slicing producer.  Pointwise multiplicity-level information and
target-measure retention produce a lower bound between the corresponding
product-pullback integrals.  The desired pullback bound is a conclusion, not
a callback. -/
theorem productPullback_levelSubset_retains_lintegral
    (mu : Measure alpha) [SFinite mu] (nu : Measure beta) [SFinite nu]
    (g : alpha × beta -> ENNReal) (hg : Measurable g)
    (base kept : Set alpha) (q C level : ENNReal)
    (hkeptMeasurable : MeasurableSet kept)
    (hbaseUpper : forall x, x ∈ base ->
      projectedSliceMultiplicity nu g x <= C * level)
    (hkeptLower : forall x, x ∈ kept ->
      level <= projectedSliceMultiplicity nu g x)
    (hmeasure : q * mu base <= mu kept) :
    q * (∫⁻ z in base ×ˢ (Set.univ : Set beta),
        g z ∂(mu.prod nu)) <=
      C * (∫⁻ z in kept ×ˢ (Set.univ : Set beta),
        g z ∂(mu.prod nu)) := by
  rw [← lintegral_projectedSliceMultiplicity_restrict nu mu g base hg,
    ← lintegral_projectedSliceMultiplicity_restrict nu mu g kept hg]
  exact levelSubset_retains_lintegral mu
    (projectedSliceMultiplicity nu g) base kept q C level
    hkeptMeasurable hbaseUpper hkeptLower hmeasure

end ProductPullbackRetention

#print axioms twistedProjection_twistedFiberChart
#print axioms twistedFiberChart_twistedFiberCoordinates
#print axioms twistedProjection_parameterLinePoint
#print axioms twistedFiberChart_preimage_twistedProjection_preimage
#print axioms lintegral_projectedSliceMultiplicity_restrict
#print axioms levelSubset_retains_lintegral
#print axioms productPullback_levelSubset_retains_lintegral

end

end FamilyStickyWZ2ProjectionSliceRetentionV1
