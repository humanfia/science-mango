import Family8Grounding.Family8PlankRetainedOwnerCutoffBallCrossV1
import Submission.Kakeya.ConvexFactoring.FrameBoxThickening
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8PlankRetainedOwnerAmbientVolumeCapV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexGeometry.FrameBoxInducedCoveringGrowth
open Family6AffinePlankAnalyticHypothesesStableV1
open Family8PlankThickControlMutualContainmentClusteringV2
open Family8PlankThickControlOwnerFiberLogBucketV2
open Family8PlankThickControlRetainedOwnerFamilyV3
open Family8PlankRetainedOwnerCubeWeightDenseBallV1

noncomputable section

universe u

variable {iota : Type u} [Fintype iota] [DecidableEq iota]
variable {a b : NNReal}

/-!
# Fixed ambient volume cap for the retained-owner packing

The ambient body is certified at unit scale.  Its actual outer witness box
therefore controls every radius-at-most-two metric thickening by the fixed
volume `125`.  The retained-mass nonvanishing input supplies a genuine source
plank and hence the scale fact `b ≤ 1`; no ambient-volume hypothesis is used.
-/

/-- Any radius-at-most-two thickening of a certified unit-scale ambient plank
has volume at most `5^3 = 125`. -/
theorem IsPlank.volume_unit_openThickening_le_oneTwentyFive
    {C r : NNReal} {K : ConvexBody Space}
    (h : IsPlank C 1 1 K) (hr : r ≤ 2) :
    volume (Metric.thickening (r : Real) (K : Set Space)) ≤ 125 := by
  rcases h with ⟨_ha, _hab, _hb, _hC, B, hBside, _hinner, houter⟩
  have hraw := B.volume_thickening_le_prod_side_add_two_mul
    (K : Set Space) houter r
  rw [hBside] at hraw
  have hwidth :
      (1 : ENNReal) + 2 * (r : ENNReal) ≤ 5 := by
    exact_mod_cast (by nlinarith : (1 : NNReal) + 2 * r ≤ 5)
  calc
    volume (Metric.thickening (r : Real) (K : Set Space)) ≤
        ((1 : ENNReal) + 2 * (r : ENNReal)) *
          (((1 : ENNReal) + 2 * (r : ENNReal)) *
            ((1 : ENNReal) + 2 * (r : ENNReal))) := by
      simpa [plankSides, Fin.prod_univ_succ] using hraw
    _ = ((1 : ENNReal) + 2 * (r : ENNReal)) ^ 3 := by ring
    _ ≤ 5 ^ (3 : Nat) := by gcongr
    _ = 125 := by norm_num

/-- Under the paper scale range, the exact ambient thickening from the
retained-owner packing-card estimate has uniformly bounded volume. -/
theorem retainedOwnerPacking_ambientThickening_volume_le_oneTwentyFive
    (D : ShadedConvexPlankFamily iota a b) {theta : NNReal}
    (C : MutualThickeningClustering D theta)
    (q : Fin (Nat.log 2 (Fintype.card iota) + 1))
    (rho : NNReal) (hrhoUpper : rho ≤ 1) (hthetaUpper : theta ≤ 1)
    (hmass : (retainedOwnerPlankFamily D C q).shading.shadingMass ≠ 0) :
    volume (Metric.thickening
      (((((rho / 2) / 3 : NNReal)) : Real) +
        ((theta * b : NNReal) : Real))
      (D.ambient : Set Space)) ≤ 125 := by
  let j := Classical.choice
    (retainedOwnerIndex_nonempty_of_shadingMass_ne_zero D C q hmass)
  have hb : b ≤ 1 := (D.all_isPlank j.1).2.2.1
  have hthetab : theta * b ≤ 1 := by
    calc
      theta * b ≤ 1 * b := by gcongr
      _ = b := one_mul b
      _ ≤ 1 := hb
  have hradius : rho / 2 / 3 + theta * b ≤ 2 := by
    nlinarith
  exact IsPlank.volume_unit_openThickening_le_oneTwentyFive
    D.ambient_is_unit_scale hradius

#print axioms IsPlank.volume_unit_openThickening_le_oneTwentyFive
#print axioms retainedOwnerPacking_ambientThickening_volume_le_oneTwentyFive

end
end Family8PlankRetainedOwnerAmbientVolumeCapV1
