import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Lemma57TubeTangencyDistanceV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32TraceTangencyScaleUpperV1

set_option autoImplicit false

open Set

namespace FamilyStickyCinematicL32Lemma57TubeDistanceBoundsV1

open FamilyStickyCinematicL32LocalTangencyV1
open FamilyStickyCinematicL32TubePairTraceV1
open FamilyStickyCinematicL32TraceTangencyScaleUpperV1
open FamilyStickyCinematicL32Lemma57TubeTangencyDistanceV1
open FamilyStickyWZ2TubeCarrierCoordinateAdapterV1
open Submission.Kakeya.ConvexGeometry

noncomputable section

/-!
# Actual Tube distance bounds for PYZ Lemma 5.7

This module supplies the elementary upper-localization facts for the
project's concrete tube coordinates.  The reduced coefficient distance is
nonnegative and satisfies the triangle inequality.  The canonical compact
tangency minimum is nonnegative and, on the normalized parameter interval,
is at most six times that coefficient distance.

All statements are proved from the coordinate definitions and the compact
minimum specification; no Lemma 5.7 good-pair conclusion is assumed.
-/

/-- The reduced coefficient distance of two actual tubes is nonnegative. -/
theorem tubePairCoefficientDistance_nonneg
    {radius : NNReal} (T U : Tube radius) :
    0 <= tubePairCoefficientDistance T U := by
  simp only [tubePairCoefficientDistance, coefficientDistance]
  positivity

/-- The reduced coefficient distance is symmetric. -/
theorem tubePairCoefficientDistance_comm
    {radius : NNReal} (T U : Tube radius) :
    tubePairCoefficientDistance T U = tubePairCoefficientDistance U T := by
  simp only [tubePairCoefficientDistance, coefficientDistance,
    tubePairDeltaA, tubePairDeltaB, tubePairDeltaD]
  rw [abs_sub_comm (tubeGraphA T), abs_sub_comm (tubeGraphB T),
    abs_sub_comm (tubeGraphD T)]

/-- Triangle inequality for the actual reduced tube coordinates. -/
theorem tubePairCoefficientDistance_triangle
    {radius : NNReal} (T U V : Tube radius) :
    tubePairCoefficientDistance T U <=
      tubePairCoefficientDistance T V +
        tubePairCoefficientDistance V U := by
  simp only [tubePairCoefficientDistance, coefficientDistance,
    tubePairDeltaA, tubePairDeltaB, tubePairDeltaD]
  have ha : |tubeGraphA T - tubeGraphA U| <=
      |tubeGraphA T - tubeGraphA V| + |tubeGraphA V - tubeGraphA U| := by
    calc
      |tubeGraphA T - tubeGraphA U| =
          |(tubeGraphA T - tubeGraphA V) +
            (tubeGraphA V - tubeGraphA U)| := by ring_nf
      _ <= _ := abs_add_le _ _
  have hb : |tubeGraphB T - tubeGraphB U| <=
      |tubeGraphB T - tubeGraphB V| + |tubeGraphB V - tubeGraphB U| := by
    calc
      |tubeGraphB T - tubeGraphB U| =
          |(tubeGraphB T - tubeGraphB V) +
            (tubeGraphB V - tubeGraphB U)| := by ring_nf
      _ <= _ := abs_add_le _ _
  have hd : |tubeGraphD T - tubeGraphD U| <=
      |tubeGraphD T - tubeGraphD V| + |tubeGraphD V - tubeGraphD U| := by
    calc
      |tubeGraphD T - tubeGraphD U| =
          |(tubeGraphD T - tubeGraphD V) +
            (tubeGraphD V - tubeGraphD U)| := by ring_nf
      _ <= _ := abs_add_le _ _
  linarith

/-- Membership of two tubes in a reduced coefficient ball of radius `3 t`
gives the literal `6 t` upper bound used in PYZ Lemma 5.7. -/
theorem tubePairCoefficientDistance_le_six_mul_of_common_center
    {radius : NNReal} (T U V : Tube radius) {t : Real}
    (hT : tubePairCoefficientDistance T V <= 3 * t)
    (hU : tubePairCoefficientDistance U V <= 3 * t) :
    tubePairCoefficientDistance T U <= 6 * t := by
  have hUV : tubePairCoefficientDistance V U <= 3 * t := by
    rw [tubePairCoefficientDistance_comm]
    exact hU
  exact (tubePairCoefficientDistance_triangle T U V).trans (by linarith)

/-- The canonical tube-pair tangency distance is nonnegative. -/
theorem tubePairAttainedTangencyDistance_nonneg
    {radius : NNReal} (T U : Tube radius)
    (f f1 f2 : Real -> Real) (A B : Real)
    (hAB : A <= B)
    (hfDeriv : forall z, z ∈ Icc A B -> HasDerivAt f (f1 z) z)
    (hf1Deriv : forall z, z ∈ Icc A B -> HasDerivAt f1 (f2 z) z) :
    0 <= tubePairAttainedTangencyDistance T U f f1 f2 A B
      hAB hfDeriv hf1Deriv := by
  obtain ⟨_theta, _htheta, hnonneg, _hdef, _hminimum⟩ :=
    tubePairAttainedTangencyDistance_spec T U f f1 f2 A B
      hAB hfDeriv hf1Deriv
  exact hnonneg

/-- On a normalized interval, the canonical tangency minimum is at most six
times the actual reduced coefficient distance. -/
theorem tubePairAttainedTangencyDistance_le_six_coefficientDistance
    {radius : NNReal} (T U : Tube radius)
    (f f1 f2 : Real -> Real) (A B : Real)
    (hAB : A <= B)
    (hfDeriv : forall z, z ∈ Icc A B -> HasDerivAt f (f1 z) z)
    (hf1Deriv : forall z, z ∈ Icc A B -> HasDerivAt f1 (f2 z) z)
    (hparameter : forall z, z ∈ Icc A B -> |z| <= 1)
    (hf : forall z, z ∈ Icc A B -> |f z| <= 2)
    (hf1 : forall z, z ∈ Icc A B -> |f1 z| <= 2) :
    tubePairAttainedTangencyDistance T U f f1 f2 A B
        hAB hfDeriv hf1Deriv <=
      6 * tubePairCoefficientDistance T U := by
  obtain ⟨theta, htheta, _hnonneg, hdef, _hminimum⟩ :=
    tubePairAttainedTangencyDistance_spec T U f f1 f2 A B
      hAB hfDeriv hf1Deriv
  have hbound := attained_traceTangencyParameter_le_six_coefficientDistance
    f f1 (tubePairDeltaA T U) (tubePairDeltaB T U)
      (tubePairDeltaD T U)
      (tubePairAttainedTangencyDistance T U f f1 f2 A B
        hAB hfDeriv hf1Deriv) theta hdef
      (hparameter theta htheta) (hf theta htheta) (hf1 theta htheta)
  simpa only [tubePairCoefficientDistance] using hbound

#print axioms tubePairCoefficientDistance_nonneg
#print axioms tubePairCoefficientDistance_comm
#print axioms tubePairCoefficientDistance_triangle
#print axioms tubePairCoefficientDistance_le_six_mul_of_common_center
#print axioms tubePairAttainedTangencyDistance_nonneg
#print axioms tubePairAttainedTangencyDistance_le_six_coefficientDistance

end

end FamilyStickyCinematicL32Lemma57TubeDistanceBoundsV1
