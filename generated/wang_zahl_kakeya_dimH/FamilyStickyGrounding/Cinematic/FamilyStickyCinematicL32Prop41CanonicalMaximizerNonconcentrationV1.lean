import FamilyStickyCinematicL32FiniteNormCriticalBallV1
import FamilyStickyCinematicL32PyzActualAllCenterCanonicalPayloadFinalV5
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true

open Set MeasureTheory

namespace FamilyStickyCinematicL32Prop41CanonicalMaximizerNonconcentrationV1

open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open FamilyStickyCinematicL32Lemma57FiniteTwoEndsMaximizerV1
open FamilyStickyCinematicL32Lemma57CriticalScaleCarrierV1
open FamilyStickyCinematicL32ContinuumActualCriticalScaleMapV1
open FamilyStickyCinematicL32FiniteIncidenceCanonicalCriticalCenterV1
open FamilyStickyCinematicL32FiniteNormCriticalBallV1
open FamilyStickyCinematicL32FiniteProjectedShadingMultiplicitySliceV1
open FamilyStickyCinematicL32ActualTubeCoefficientDistancesV1
open FamilyStickyCinematicL32ActualTubeCoefficientMetricV1
open FamilyStickyCinematicL32ActualProjectedNormSourceFamilyV1
open FamilyStickyCinematicL32PyzActualAllCenterCanonicalPayloadFinalV5
open FamilyStickyCinematicL32PyzE2DyadicDegreeWindowV1

noncomputable section

universe u v

/-!
# Quantitative non-concentration from the canonical norm maximizer

The finite score is exactly `#B(g,r) * r ^ (-exponent)`.  Consequently the
canonical maximizer gives the weighted form of the paper's non-concentration
inequality at every real radius in the full interval.  Positivity of the two
scales then converts it to the ratio form
`#B(g,r) <= (r / t) ^ exponent * #B(center,t)`.

This module packages that conclusion with a high payload, but does not identify
the resulting norm ball with any later coarse family or assert a width/breadth
property for such a family.
-/

/-- Exact weighted-ball domination supplied by the canonical maximizer. -/
theorem finiteNormCriticalBall_weighted_nonconcentration
    {alpha : Type*} (family : Finset alpha)
    (distance : alpha -> alpha -> Real)
    {delta ceiling exponent radius : Real}
    (hfamily : family.Nonempty)
    (hself : forall center, center ∈ family ->
      distance center center <= delta)
    (hdelta : 0 < delta) (hdeltaCeiling : delta <= ceiling)
    (hexponent : 0 <= exponent)
    (hradiusLower : delta <= radius) (hradiusUpper : radius <= ceiling)
    (testCenter : alpha) (htestCenter : testCenter ∈ family) :
    (finiteBallCount family distance radius testCenter : Real) *
        radius ^ (-exponent) <=
      ((finiteNormCriticalBall family distance delta ceiling exponent
          hfamily).card : Real) *
        (finiteCriticalMaximizerScale family distance delta ceiling exponent
          hfamily) ^ (-exponent) := by
  have hdom := canonicalCriticalMaximizer_dominates_on_Icc
    family distance hfamily hself hdelta hdeltaCeiling hexponent
      radius hradiusLower hradiusUpper testCenter htestCenter
  simpa only [finiteTwoEndsScore, finiteNormCriticalBall_card,
    finiteCriticalMaximizerScale, finiteCriticalMaximizerCenter] using hdom

/-- Paper-form non-concentration.  Here `t` is the canonical maximizing scale,
and the right cardinality is literally `#B(center,t)`. -/
theorem finiteNormCriticalBall_card_le_ratio_rpow
    {alpha : Type*} (family : Finset alpha)
    (distance : alpha -> alpha -> Real)
    {delta ceiling exponent radius : Real}
    (hfamily : family.Nonempty)
    (hself : forall center, center ∈ family ->
      distance center center <= delta)
    (hdelta : 0 < delta) (hdeltaCeiling : delta <= ceiling)
    (hexponent : 0 <= exponent)
    (hradiusLower : delta <= radius) (hradiusUpper : radius <= ceiling)
    (testCenter : alpha) (htestCenter : testCenter ∈ family) :
    (finiteBallCount family distance radius testCenter : Real) <=
      (radius /
          finiteCriticalMaximizerScale family distance delta ceiling exponent
            hfamily) ^ exponent *
        ((finiteNormCriticalBall family distance delta ceiling exponent
          hfamily).card : Real) := by
  let criticalScale :=
    finiteCriticalMaximizerScale family distance delta ceiling exponent hfamily
  have hradiusPos : 0 < radius := hdelta.trans_le hradiusLower
  have hcriticalScaleLower : delta <= criticalScale := by
    exact (finiteCriticalMaximizerScale_bounds family distance hfamily
      hdeltaCeiling).1
  have hcriticalScalePos : 0 < criticalScale :=
    hdelta.trans_le hcriticalScaleLower
  have hweighted := finiteNormCriticalBall_weighted_nonconcentration
    family distance hfamily hself hdelta hdeltaCeiling hexponent
      hradiusLower hradiusUpper testCenter htestCenter
  change
    (finiteBallCount family distance radius testCenter : Real) *
        radius ^ (-exponent) <=
      ((finiteNormCriticalBall family distance delta ceiling exponent
          hfamily).card : Real) * criticalScale ^ (-exponent) at hweighted
  change
    (finiteBallCount family distance radius testCenter : Real) <=
      (radius / criticalScale) ^ exponent *
        ((finiteNormCriticalBall family distance delta ceiling exponent
          hfamily).card : Real)
  calc
    (finiteBallCount family distance radius testCenter : Real) =
        ((finiteBallCount family distance radius testCenter : Real) *
          radius ^ (-exponent)) * radius ^ exponent := by
      rw [mul_assoc, <- Real.rpow_add hradiusPos]
      simp
    _ <= (((finiteNormCriticalBall family distance delta ceiling exponent
          hfamily).card : Real) * criticalScale ^ (-exponent)) *
          radius ^ exponent :=
      mul_le_mul_of_nonneg_right hweighted
        (Real.rpow_nonneg hradiusPos.le exponent)
    _ = (radius / criticalScale) ^ exponent *
        ((finiteNormCriticalBall family distance delta ceiling exponent
          hfamily).card : Real) := by
      rw [Real.div_rpow hradiusPos.le hcriticalScalePos.le,
        Real.rpow_neg hcriticalScalePos.le]
      simp only [div_eq_mul_inv]
      ring

/-- A small record which can be retained together with a downstream payload.
Its fields are the genuine source hypotheses; both non-concentration forms are
derived below rather than stored as callbacks. -/
structure CanonicalNormNonconcentrationData (alpha : Type*) where
  family : Finset alpha
  distance : alpha -> alpha -> Real
  delta : Real
  ceiling : Real
  exponent : Real
  family_nonempty : family.Nonempty
  self_le_delta : forall center, center ∈ family ->
    distance center center <= delta
  delta_pos : 0 < delta
  delta_le_ceiling : delta <= ceiling
  exponent_nonneg : 0 <= exponent

namespace CanonicalNormNonconcentrationData

def criticalScale {alpha : Type*}
    (D : CanonicalNormNonconcentrationData alpha) : Real :=
  finiteCriticalMaximizerScale D.family D.distance D.delta D.ceiling D.exponent
    D.family_nonempty

def criticalCenter {alpha : Type*}
    (D : CanonicalNormNonconcentrationData alpha) : alpha :=
  finiteCriticalMaximizerCenter D.family D.distance D.delta D.ceiling D.exponent
    D.family_nonempty

def criticalBall {alpha : Type*}
    (D : CanonicalNormNonconcentrationData alpha) : Finset alpha :=
  finiteNormCriticalBall D.family D.distance D.delta D.ceiling D.exponent
    D.family_nonempty

theorem weighted_nonconcentration {alpha : Type*}
    (D : CanonicalNormNonconcentrationData alpha)
    {radius : Real} (hradiusLower : D.delta <= radius)
    (hradiusUpper : radius <= D.ceiling)
    (testCenter : alpha) (htestCenter : testCenter ∈ D.family) :
    (finiteBallCount D.family D.distance radius testCenter : Real) *
        radius ^ (-D.exponent) <=
      ((D.criticalBall.card : Nat) : Real) *
        D.criticalScale ^ (-D.exponent) := by
  exact finiteNormCriticalBall_weighted_nonconcentration
    D.family D.distance D.family_nonempty D.self_le_delta D.delta_pos
      D.delta_le_ceiling D.exponent_nonneg hradiusLower hradiusUpper
      testCenter htestCenter

theorem card_le_ratio_rpow {alpha : Type*}
    (D : CanonicalNormNonconcentrationData alpha)
    {radius : Real} (hradiusLower : D.delta <= radius)
    (hradiusUpper : radius <= D.ceiling)
    (testCenter : alpha) (htestCenter : testCenter ∈ D.family) :
    (finiteBallCount D.family D.distance radius testCenter : Real) <=
      (radius / D.criticalScale) ^ D.exponent *
        ((D.criticalBall.card : Nat) : Real) := by
  exact finiteNormCriticalBall_card_le_ratio_rpow
    D.family D.distance D.family_nonempty D.self_le_delta D.delta_pos
      D.delta_le_ceiling D.exponent_nonneg hradiusLower hradiusUpper
      testCenter htestCenter

end CanonicalNormNonconcentrationData

/-! The existing positive-centre payload does not contain its preceding norm
maximizer.  This honest wrapper records the two missing facts needed to retain
that maximizer with a high payload: nonemptiness of the actual local norm
family at `payload.q`, and nonnegativity of the norm exponent. -/

/-- A high positive-centre payload together with the actual norm-maximizer data
at its selected point. -/
structure ActualHighPayloadWithNormNonconcentration
    {point : Type v} [MeasurableSpace point]
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    (mu : Measure point) (base : Set point) (hbase : MeasurableSet base)
    (fine : UniformTubeFamily radius iota)
    (physical : FiniteProjectedShading point iota)
    (f f1 f2 : Real -> Real) (outerA outerB : Real)
    (hOuter : outerA <= outerB)
    (hf : forall z, HasDerivAt f (f1 z) z)
    (hf1 : forall z, HasDerivAt f1 (f2 z) z)
    (globalScale : Real) (globalCenter : Tube radius)
    (tangencyExponent normExponent : Real) (logCount : Nat) where
  payload : ActualPositiveCenterCanonicalPayload mu base hbase fine physical
    f f1 f2 outerA outerB hOuter hf hf1 globalScale globalCenter
      tangencyExponent
  high : 24 * logCount <= pyzE2DegreeLower payload.finalLabel
  normFamily_nonempty :
    (actualProjectedAmbientCriticalFamily fine physical.ambient
      (physical.activeAtPoint payload.q)).Nonempty
  radius_pos : 0 < radius
  radius_le_sixteen : (radius : Real) <= 16
  normExponent_nonneg : 0 <= normExponent

namespace ActualHighPayloadWithNormNonconcentration

/-- The packaged actual coefficient-distance maximizer data. -/
def normData
    {point : Type v} [MeasurableSpace point]
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    {mu : Measure point} {base : Set point} {hbase : MeasurableSet base}
    {fine : UniformTubeFamily radius iota}
    {physical : FiniteProjectedShading point iota}
    {f f1 f2 : Real -> Real} {outerA outerB : Real}
    {hOuter : outerA <= outerB}
    {hf : forall z, HasDerivAt f (f1 z) z}
    {hf1 : forall z, HasDerivAt f1 (f2 z) z}
    {globalScale : Real} {globalCenter : Tube radius}
    {tangencyExponent normExponent : Real} {logCount : Nat}
    (P : ActualHighPayloadWithNormNonconcentration mu base hbase fine physical
      f f1 f2 outerA outerB hOuter hf hf1 globalScale globalCenter
        tangencyExponent normExponent logCount) :
    CanonicalNormNonconcentrationData (Tube radius) where
  family := actualProjectedAmbientCriticalFamily fine physical.ambient
    (physical.activeAtPoint P.payload.q)
  distance := projectedTubePairCoefficientDistance
  delta := radius
  ceiling := 16
  exponent := normExponent
  family_nonempty := P.normFamily_nonempty
  self_le_delta := by
    intro T _hT
    rw [projectedTubePairCoefficientDistance_self]
    exact_mod_cast P.radius_pos.le
  delta_pos := by exact_mod_cast P.radius_pos
  delta_le_ceiling := P.radius_le_sixteen
  exponent_nonneg := P.normExponent_nonneg

/-- The selected point of every actual positive-centre payload still belongs
to its input base cell. -/
theorem payload_q_mem_base
    {point : Type v} [MeasurableSpace point]
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    {mu : Measure point} {base : Set point} {hbase : MeasurableSet base}
    {fine : UniformTubeFamily radius iota}
    {physical : FiniteProjectedShading point iota}
    {f f1 f2 : Real -> Real} {outerA outerB : Real}
    {hOuter : outerA <= outerB}
    {hf : forall z, HasDerivAt f (f1 z) z}
    {hf1 : forall z, HasDerivAt f1 (f2 z) z}
    {globalScale : Real} {globalCenter : Tube radius}
    {tangencyExponent : Real}
    (payload : ActualPositiveCenterCanonicalPayload mu base hbase fine physical
      f f1 f2 outerA outerB hOuter hf hf1 globalScale globalCenter
        tangencyExponent) :
    payload.q ∈ base := by
  rcases payload.certificate with
    ⟨_hfinalLabel, hq, _hmeasure, _hEtPos, hEtSubset, _htangencyBin,
      _hE2Pos, _hE2Measurable, hE2Subset, _hactive⟩
  exact hEtSubset (hE2Subset hq)

/-- Retain the genuine local norm maximizer beside an existing high payload.
The local-family producer is evaluated at the payload proved base member;
no ball estimate is accepted as an input. -/
def ofPayload
    {point : Type v} [MeasurableSpace point]
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    {mu : Measure point} {base : Set point} {hbase : MeasurableSet base}
    {fine : UniformTubeFamily radius iota}
    {physical : FiniteProjectedShading point iota}
    {f f1 f2 : Real -> Real} {outerA outerB : Real}
    {hOuter : outerA <= outerB}
    {hf : forall z, HasDerivAt f (f1 z) z}
    {hf1 : forall z, HasDerivAt f1 (f2 z) z}
    {globalScale : Real} {globalCenter : Tube radius}
    {tangencyExponent normExponent : Real} {logCount : Nat}
    (payload : ActualPositiveCenterCanonicalPayload mu base hbase fine physical
      f f1 f2 outerA outerB hOuter hf hf1 globalScale globalCenter
        tangencyExponent)
    (high : 24 * logCount <= pyzE2DegreeLower payload.finalLabel)
    (hradius : 0 < radius) (hradiusSixteen : (radius : Real) <= 16)
    (hnormExponent : 0 <= normExponent)
    (hlocalFamily : forall x, x ∈ base ->
      (actualProjectedAmbientCriticalFamily fine physical.ambient
        (physical.activeAtPoint x)).Nonempty) :
    ActualHighPayloadWithNormNonconcentration mu base hbase fine physical
      f f1 f2 outerA outerB hOuter hf hf1 globalScale globalCenter
        tangencyExponent normExponent logCount where
  payload := payload
  high := high
  normFamily_nonempty := hlocalFamily payload.q (payload_q_mem_base payload)
  radius_pos := hradius
  radius_le_sixteen := hradiusSixteen
  normExponent_nonneg := hnormExponent

end ActualHighPayloadWithNormNonconcentration

#print axioms finiteNormCriticalBall_weighted_nonconcentration
#print axioms finiteNormCriticalBall_card_le_ratio_rpow
#print axioms CanonicalNormNonconcentrationData
#print axioms CanonicalNormNonconcentrationData.weighted_nonconcentration
#print axioms CanonicalNormNonconcentrationData.card_le_ratio_rpow
#print axioms ActualHighPayloadWithNormNonconcentration
#print axioms ActualHighPayloadWithNormNonconcentration.normData
#print axioms ActualHighPayloadWithNormNonconcentration.payload_q_mem_base
#print axioms ActualHighPayloadWithNormNonconcentration.ofPayload

end

end FamilyStickyCinematicL32Prop41CanonicalMaximizerNonconcentrationV1
