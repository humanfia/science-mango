import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32TraceTangencyMinimizerV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32TubePairTraceV1

set_option autoImplicit false

open Set

namespace FamilyStickyCinematicL32Lemma57TubeTangencyDistanceV1

open FamilyStickyCinematicL32TraceTangencyMinimizerV1
open FamilyStickyCinematicL32TubePairTraceV1
open FamilyStickyWZ2TubeCarrierCoordinateAdapterV1
open Submission.Kakeya.ConvexGeometry

noncomputable section

/-!
# Canonical attained tangency distance for actual tube pairs

PYZ Definition 3.7 uses the minimum of the value--first-jet cost on the
compact middle interval.  This module packages the compactness theorem as
a canonical scalar distance.  The value, minimizing point, nonnegativity,
and universal lower bound are all selected from the proved minimizer
theorem; none is accepted as a callback.
-/

/-- Full data carried by an attained trace tangency minimum. -/
structure AttainedTraceTangencyData
    (f f1 : Real -> Real) (da db dd A B : Real) where
  value : Real
  point : Real
  value_nonneg : 0 <= value
  point_mem : point ∈ Icc A B
  value_eq : value = traceTangencyCost f f1 da db dd point
  isMinimum : forall theta, theta ∈ Icc A B ->
    value <= traceTangencyCost f f1 da db dd theta

/-- Compactness and the actual derivative certificates construct the full
attained-minimum data. -/
noncomputable def attainedTraceTangencyData
    (f f1 f2 : Real -> Real) (da db dd A B : Real)
    (hAB : A <= B)
    (hfDeriv : forall z, z ∈ Icc A B -> HasDerivAt f (f1 z) z)
    (hf1Deriv : forall z, z ∈ Icc A B -> HasDerivAt f1 (f2 z) z) :
    AttainedTraceTangencyData f f1 da db dd A B := by
  classical
  let hexists :=
    exists_trace_tangencyParameter_with_minimizer
      f f1 f2 da db dd hAB hfDeriv hf1Deriv
  let Delta := Classical.choose hexists
  let hDeltaExists := Classical.choose_spec hexists
  let thetaDelta := Classical.choose hDeltaExists
  have hspec := Classical.choose_spec hDeltaExists
  exact
    { value := Delta
      point := thetaDelta
      value_nonneg := hspec.1
      point_mem := hspec.2.1
      value_eq := hspec.2.2.1
      isMinimum := hspec.2.2.2 }

/-- The canonical scalar PYZ tangency distance. -/
noncomputable def attainedTraceTangencyDistance
    (f f1 f2 : Real -> Real) (da db dd A B : Real)
    (hAB : A <= B)
    (hfDeriv : forall z, z ∈ Icc A B -> HasDerivAt f (f1 z) z)
    (hf1Deriv : forall z, z ∈ Icc A B -> HasDerivAt f1 (f2 z) z) : Real :=
  (attainedTraceTangencyData f f1 f2 da db dd A B
    hAB hfDeriv hf1Deriv).value

/-- The selected point attaining the canonical distance. -/
noncomputable def attainedTraceTangencyPoint
    (f f1 f2 : Real -> Real) (da db dd A B : Real)
    (hAB : A <= B)
    (hfDeriv : forall z, z ∈ Icc A B -> HasDerivAt f (f1 z) z)
    (hf1Deriv : forall z, z ∈ Icc A B -> HasDerivAt f1 (f2 z) z) : Real :=
  (attainedTraceTangencyData f f1 f2 da db dd A B
    hAB hfDeriv hf1Deriv).point

/-- Complete specification of the canonical value and point. -/
theorem attainedTraceTangencyDistance_spec
    (f f1 f2 : Real -> Real) (da db dd A B : Real)
    (hAB : A <= B)
    (hfDeriv : forall z, z ∈ Icc A B -> HasDerivAt f (f1 z) z)
    (hf1Deriv : forall z, z ∈ Icc A B -> HasDerivAt f1 (f2 z) z) :
    let Delta := attainedTraceTangencyDistance f f1 f2 da db dd A B
      hAB hfDeriv hf1Deriv
    let thetaDelta := attainedTraceTangencyPoint f f1 f2 da db dd A B
      hAB hfDeriv hf1Deriv
    0 <= Delta ∧ thetaDelta ∈ Icc A B ∧
      Delta = traceTangencyCost f f1 da db dd thetaDelta ∧
      forall theta, theta ∈ Icc A B ->
        Delta <= traceTangencyCost f f1 da db dd theta := by
  dsimp only [attainedTraceTangencyDistance, attainedTraceTangencyPoint]
  exact ⟨(attainedTraceTangencyData f f1 f2 da db dd A B
      hAB hfDeriv hf1Deriv).value_nonneg,
    (attainedTraceTangencyData f f1 f2 da db dd A B
      hAB hfDeriv hf1Deriv).point_mem,
    (attainedTraceTangencyData f f1 f2 da db dd A B
      hAB hfDeriv hf1Deriv).value_eq,
    (attainedTraceTangencyData f f1 f2 da db dd A B
      hAB hfDeriv hf1Deriv).isMinimum⟩

/-- Any other explicitly attained global minimum has the same scalar value
as the canonical one.  This identifies the existential `DeltaPair` used by
Lemma 5.8 with the distance used in Lemma 5.7. -/
theorem eq_attainedTraceTangencyDistance_of_isMinimum
    (f f1 f2 : Real -> Real) (da db dd A B Delta thetaDelta : Real)
    (hAB : A <= B)
    (hfDeriv : forall z, z ∈ Icc A B -> HasDerivAt f (f1 z) z)
    (hf1Deriv : forall z, z ∈ Icc A B -> HasDerivAt f1 (f2 z) z)
    (hthetaDelta : thetaDelta ∈ Icc A B)
    (hDeltaDef : Delta = traceTangencyCost f f1 da db dd thetaDelta)
    (hminimum : forall theta, theta ∈ Icc A B ->
      Delta <= traceTangencyCost f f1 da db dd theta) :
    Delta = attainedTraceTangencyDistance f f1 f2 da db dd A B
      hAB hfDeriv hf1Deriv := by
  obtain ⟨_hcanonicalNonneg, hcanonicalPoint,
      hcanonicalDef, hcanonicalMinimum⟩ :=
    attainedTraceTangencyDistance_spec f f1 f2 da db dd A B
      hAB hfDeriv hf1Deriv
  apply le_antisymm
  · rw [hcanonicalDef]
    exact hminimum _ hcanonicalPoint
  · rw [hDeltaDef]
    exact hcanonicalMinimum _ hthetaDelta

/-- Canonical tangency distance of an ordered pair of actual project
tubes, using the reduced `(a,b,d)` trace in one fixed/approximate `c`
bucket. -/
noncomputable def tubePairAttainedTangencyDistance
    {radius : NNReal} (T U : Tube radius)
    (f f1 f2 : Real -> Real) (A B : Real)
    (hAB : A <= B)
    (hfDeriv : forall z, z ∈ Icc A B -> HasDerivAt f (f1 z) z)
    (hf1Deriv : forall z, z ∈ Icc A B -> HasDerivAt f1 (f2 z) z) : Real :=
  attainedTraceTangencyDistance f f1 f2
    (tubePairDeltaA T U) (tubePairDeltaB T U) (tubePairDeltaD T U)
    A B hAB hfDeriv hf1Deriv

/-- The canonical tube-pair distance is attained and globally minimal on
the requested compact interval. -/
theorem tubePairAttainedTangencyDistance_spec
    {radius : NNReal} (T U : Tube radius)
    (f f1 f2 : Real -> Real) (A B : Real)
    (hAB : A <= B)
    (hfDeriv : forall z, z ∈ Icc A B -> HasDerivAt f (f1 z) z)
    (hf1Deriv : forall z, z ∈ Icc A B -> HasDerivAt f1 (f2 z) z) :
    exists thetaDelta, thetaDelta ∈ Icc A B ∧
      0 <= tubePairAttainedTangencyDistance T U f f1 f2 A B
        hAB hfDeriv hf1Deriv ∧
      tubePairAttainedTangencyDistance T U f f1 f2 A B
          hAB hfDeriv hf1Deriv =
        traceTangencyCost f f1
          (tubePairDeltaA T U) (tubePairDeltaB T U)
          (tubePairDeltaD T U) thetaDelta ∧
      forall theta, theta ∈ Icc A B ->
        tubePairAttainedTangencyDistance T U f f1 f2 A B
            hAB hfDeriv hf1Deriv <=
          traceTangencyCost f f1
            (tubePairDeltaA T U) (tubePairDeltaB T U)
            (tubePairDeltaD T U) theta := by
  obtain ⟨hDelta, htheta, hdef, hminimum⟩ :=
    attainedTraceTangencyDistance_spec f f1 f2
      (tubePairDeltaA T U) (tubePairDeltaB T U) (tubePairDeltaD T U)
      A B hAB hfDeriv hf1Deriv
  exact ⟨attainedTraceTangencyPoint f f1 f2
      (tubePairDeltaA T U) (tubePairDeltaB T U) (tubePairDeltaD T U)
      A B hAB hfDeriv hf1Deriv,
    htheta, hDelta, hdef, hminimum⟩

#print axioms attainedTraceTangencyData
#print axioms attainedTraceTangencyDistance
#print axioms attainedTraceTangencyDistance_spec
#print axioms eq_attainedTraceTangencyDistance_of_isMinimum
#print axioms tubePairAttainedTangencyDistance
#print axioms tubePairAttainedTangencyDistance_spec

end

end FamilyStickyCinematicL32Lemma57TubeTangencyDistanceV1
