import Family8Grounding.Family8SelectedOccurrenceNormalizedCanonicalGlobalDeltaEq45ControlV1
import Family8Grounding.Family8SelectedOccurrenceOuterFamilyVolumeV1
import Family8Grounding.Family8SelectedOuterCanonicalDeltaScalarCancellationV1
import Mathlib.Tactic

/-!
# Card-free canonical-Delta and thick-aspect cancellation

This file joins the exact selected-occurrence outer-family volume identity to
the canonical normalized global `Delta`.  The source and outer Frostman
constants remain explicit producer outputs: the proof only rewrites their two
displayed defining equalities and checks the legitimate `V`, `B`, and `d`
cancellations.  The retained outer body-volume sum is the literal sum on the
same `Rside`; it is never replaced by a cardinality envelope.

The second lemma records the coupled cancellation which is useful after
Equation (45): the `b / a` aspect ratio inside the honest thickening constant
is paid by the adjacent `a / b` factor.  Thus the canonical `Delta` bound
enters with no additional aspect-ratio loss.
-/

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8SelectedOccurrenceCanonicalDeltaThickAspectAdapterV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.Uniformity
open Family8AmbientFamilyVolumeDensityV2
open Family8Prop51SelectedFineBlockDensityNormalizedFrostmanV1
open Family8SelectedOccurrenceDensityFrostmanV1
open Family8SelectedOccurrenceNormalizedCanonicalGlobalDeltaEq45ControlV1
open Family8SelectedOccurrenceOuterFamilyVolumeV1
open Family8SelectedOuterCanonicalDeltaScalarCancellationV1
open Family8UniqueOwnerLocalDeltaMaxThickControlV1

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000

local instance (p : Prop) : Decidable p := Classical.propDecidable p

universe u

variable {delta : NNReal} {iota : Type u}
  [Fintype iota] [DecidableEq iota]
  {fine : UniformTubeFamily delta iota}
  {active : Finset iota}

variable
  (P : GreedyDensityPartition fine.bodyFamily
    (hullCandidates active) (hullContainer fine.bodyFamily) active)

/-- The canonical normalized global `Delta` of the exact selected occurrence
outer family is bounded by the card-free source Katz--Tao coefficient.

`V`, `B`, `d`, `sourceCF`, and `outerCF` are kept as the literal names used by
the upstream producers.  The equality `hV` identifies `V` with the actual
ambient volume, while `hRsideBodyVolume` is the only comparison involving
`B`: its left side is the exact winning-body volume on this same `Rside`.
-/
theorem selectedOccurrenceNormalizedOuterCanonicalDelta_le_two_mul_sourceKT_mul_densityInverse_of_producer
    (Rside : Finset (Fin (blocks fine.bodyFamily P).length))
    (ambient : ConvexBody Space)
    (sourceKT V d B sourceCF outerCF : ENNReal)
    (hsourceKTTop : sourceKT ≠ ∞)
    (hV : V = volume (ambient : Set Space))
    (hV0 : V ≠ 0) (hVTop : V ≠ ∞)
    (hd0 : d ≠ 0) (hdTop : d ≠ ∞)
    (hB0 : B ≠ 0) (hBTop : B ≠ ∞)
    (hRsideBodyVolume : prop51SubselectedBodyVolume P Rside ≤ B)
    (hsourceCF : sourceCF = sourceKT * V * d⁻¹ * B⁻¹)
    (houterCF : outerCF = sourceCF * (2 * d) * d⁻¹) :
    (selectedOccurrenceNormalizedOuterCanonicalDelta
        P Rside ambient outerCF : ENNReal) ≤
      2 * sourceKT * d⁻¹ := by
  have hambientVolume0 : volume (ambient : Set Space) ≠ 0 := by
    simpa only [hV] using hV0
  have hsourceCFTop : sourceCF ≠ ∞ := by
    rw [hsourceCF]
    exact ENNReal.mul_ne_top
      (ENNReal.mul_ne_top
        (ENNReal.mul_ne_top hsourceKTTop hVTop)
        (ENNReal.inv_ne_top.mpr hd0))
      (ENNReal.inv_ne_top.mpr hB0)
  have houterCFTop : outerCF ≠ ∞ := by
    rw [houterCF]
    exact ENNReal.mul_ne_top
      (ENNReal.mul_ne_top hsourceCFTop
        (ENNReal.mul_ne_top (by norm_num) hdTop))
      (ENNReal.inv_ne_top.mpr hd0)
  rw [selectedOccurrenceNormalizedOuterCanonicalDelta_coe
    P Rside ambient outerCF houterCFTop hambientVolume0]
  apply outerCF_mul_ambientDensity_le_two_mul_sourceKT_mul_inv
    sourceKT V d B (prop51SubselectedBodyVolume P Rside)
      sourceCF outerCF
      (ambientFamilyVolumeDensity
        (selectedOccurrenceOuterFamily P Rside) ambient)
      hV0 hVTop hd0 hdTop hB0 hBTop hRsideBodyVolume
      hsourceCF houterCF
  unfold ambientFamilyVolumeDensity
  rw [selectedOccurrenceOuterFamily_familyVolume_eq_prop51SubselectedBodyVolume
    P Rside]
  simpa only [hV] using
    (le_refl (prop51SubselectedBodyVolume P Rside /
      volume (ambient : Set Space)))

/-- In the exact-`Rside` source producer, the normalization denominator is
itself the selected winning-body volume.  This wrapper removes even the
reflexive body-volume comparison from the call site while retaining every
nonzero/non-top cancellation premise explicitly. -/
theorem selectedOccurrenceNormalizedOuterCanonicalDelta_le_two_mul_sourceKT_mul_densityInverse_exactRside
    (Rside : Finset (Fin (blocks fine.bodyFamily P).length))
    (ambient : ConvexBody Space)
    (sourceKT V d sourceCF outerCF : ENNReal)
    (hsourceKTTop : sourceKT ≠ ∞)
    (hV : V = volume (ambient : Set Space))
    (hV0 : V ≠ 0) (hVTop : V ≠ ∞)
    (hd0 : d ≠ 0) (hdTop : d ≠ ∞)
    (hB0 : prop51SubselectedBodyVolume P Rside ≠ 0)
    (hBTop : prop51SubselectedBodyVolume P Rside ≠ ∞)
    (hsourceCF : sourceCF = sourceKT * V * d⁻¹ *
      (prop51SubselectedBodyVolume P Rside)⁻¹)
    (houterCF : outerCF = sourceCF * (2 * d) * d⁻¹) :
    (selectedOccurrenceNormalizedOuterCanonicalDelta
        P Rside ambient outerCF : ENNReal) ≤
      2 * sourceKT * d⁻¹ := by
  exact
    selectedOccurrenceNormalizedOuterCanonicalDelta_le_two_mul_sourceKT_mul_densityInverse_of_producer
      P Rside ambient sourceKT V d
      (prop51SubselectedBodyVolume P Rside) sourceCF outerCF
      hsourceKTTop hV hV0 hVTop hd0 hdTop hB0 hBTop le_rfl
      hsourceCF houterCF

/-- The honest `C = 576` thickening coefficient and its adjacent aspect
factor cancel.  The coefficient hypothesis is deliberately stated in
`ENNReal`, so the canonical-`Delta` estimate above can be passed directly.
-/
theorem uniqueOwnerLocalDeltaThickM_576_mul_aspectRatio_le_of_deltaCoefficient
    (Delta a b : NNReal) (sourceKT d : ENNReal)
    (ha : 0 < a) (hab : a ≤ b)
    (hDelta : (Delta : ENNReal) ≤ 2 * sourceKT * d⁻¹) :
    (uniqueOwnerLocalDeltaThickM 576 Delta a b : ENNReal) *
        ((a / b : NNReal) : ENNReal) ≤
      max 1
        (2 * (27 * (576 : ENNReal) ^ 3) * sourceKT * d⁻¹) := by
  have hb : 0 < b := ha.trans_le hab
  have hratioLeOne : a / b ≤ (1 : NNReal) := by
    exact (div_le_iff₀ hb).2 (by simpa using hab)
  have hratioCancel : (b / a) * (a / b) = (1 : NNReal) := by
    field_simp [ha.ne', hb.ne']
  rcases le_total
      (27 * (576 : NNReal) ^ 3 * Delta * (b / a)) 1 with hsmall | hlarge
  · rw [uniqueOwnerLocalDeltaThickM, max_eq_left hsmall]
    simp only [ENNReal.coe_one, one_mul]
    calc
      ((a / b : NNReal) : ENNReal) ≤ 1 := by exact_mod_cast hratioLeOne
      _ ≤ max 1
          (2 * (27 * (576 : ENNReal) ^ 3) * sourceKT * d⁻¹) :=
        le_max_left _ _
  · rw [uniqueOwnerLocalDeltaThickM, max_eq_right hlarge]
    have hleft :
        ((27 * (576 : NNReal) ^ 3 * Delta * (b / a) : NNReal) : ENNReal) *
            ((a / b : NNReal) : ENNReal) =
          ((27 * (576 : NNReal) ^ 3 * Delta : NNReal) : ENNReal) := by
      rw [← ENNReal.coe_mul]
      congr 1
      calc
        (27 * (576 : NNReal) ^ 3 * Delta * (b / a)) * (a / b) =
            (27 * (576 : NNReal) ^ 3 * Delta) *
              ((b / a) * (a / b)) := by ring
        _ = 27 * (576 : NNReal) ^ 3 * Delta := by
          rw [hratioCancel, mul_one]
    rw [hleft]
    calc
      ((27 * (576 : NNReal) ^ 3 * Delta : NNReal) : ENNReal) =
          (27 * (576 : ENNReal) ^ 3) * (Delta : ENNReal) := by
        simp only [ENNReal.coe_mul, ENNReal.coe_pow, ENNReal.coe_ofNat]
      _ ≤ (27 * (576 : ENNReal) ^ 3) *
          (2 * sourceKT * d⁻¹) := mul_le_mul' le_rfl hDelta
      _ = 2 * (27 * (576 : ENNReal) ^ 3) * sourceKT * d⁻¹ := by ring
      _ ≤ max 1
          (2 * (27 * (576 : ENNReal) ^ 3) * sourceKT * d⁻¹) :=
        le_max_right _ _

/-- Equation (45)-facing spelling of the coupled scalar bound.  Its aspect
ratio is written as an `ENNReal` quotient, exactly as in
`convexPlankFrostmanFactor`. -/
theorem uniqueOwnerLocalDeltaThickM_576_mul_ennrealAspectRatio_le_of_deltaCoefficient
    (Delta a b : NNReal) (sourceKT d : ENNReal)
    (ha : 0 < a) (hab : a ≤ b)
    (hDelta : (Delta : ENNReal) ≤ 2 * sourceKT * d⁻¹) :
    (uniqueOwnerLocalDeltaThickM 576 Delta a b : ENNReal) *
        ((a : ENNReal) / (b : ENNReal)) ≤
      max 1
        (2 * (27 * (576 : ENNReal) ^ 3) * sourceKT * d⁻¹) := by
  have hb : b ≠ 0 := (ha.trans_le hab).ne'
  simpa only [ENNReal.coe_div hb] using
    uniqueOwnerLocalDeltaThickM_576_mul_aspectRatio_le_of_deltaCoefficient
      Delta a b sourceKT d ha hab hDelta

/-- Powered coupled loss ready for the honest Family 6 to Equation (45)
comparison.  No upper bound on `beta` and no finiteness of the right-hand
side are needed; only monotonicity at the nonnegative exponent `beta / 2` is
used. -/
theorem uniqueOwnerLocalDeltaThickM_576_mul_ennrealAspectRatio_rpow_le_of_deltaCoefficient
    (Delta a b : NNReal) (sourceKT d : ENNReal) (beta : Real)
    (ha : 0 < a) (hab : a ≤ b) (hbeta : 0 ≤ beta)
    (hDelta : (Delta : ENNReal) ≤ 2 * sourceKT * d⁻¹) :
    (((uniqueOwnerLocalDeltaThickM 576 Delta a b : ENNReal) *
        ((a : ENNReal) / (b : ENNReal))) ^ (beta / 2)) ≤
      (max 1
        (2 * (27 * (576 : ENNReal) ^ 3) * sourceKT * d⁻¹)) ^
          (beta / 2) := by
  apply ENNReal.rpow_le_rpow
    (uniqueOwnerLocalDeltaThickM_576_mul_ennrealAspectRatio_le_of_deltaCoefficient
      Delta a b sourceKT d ha hab hDelta)
  linarith

/-- Direct combined form for the exact selected occurrence set.  It is the
card-free quantity consumed by the final loss ledger: the canonical global
`Delta` and the `a / b` in the Equation (45) factor are discharged together.
-/
theorem selectedOccurrenceCanonicalThickM_576_mul_aspectRatio_le_exactRside
    (Rside : Finset (Fin (blocks fine.bodyFamily P).length))
    (ambient : ConvexBody Space)
    (sourceKT V d sourceCF outerCF : ENNReal)
    (hsourceKTTop : sourceKT ≠ ∞)
    (hV : V = volume (ambient : Set Space))
    (hV0 : V ≠ 0) (hVTop : V ≠ ∞)
    (hd0 : d ≠ 0) (hdTop : d ≠ ∞)
    (hB0 : prop51SubselectedBodyVolume P Rside ≠ 0)
    (hBTop : prop51SubselectedBodyVolume P Rside ≠ ∞)
    (hsourceCF : sourceCF = sourceKT * V * d⁻¹ *
      (prop51SubselectedBodyVolume P Rside)⁻¹)
    (houterCF : outerCF = sourceCF * (2 * d) * d⁻¹)
    (a b : NNReal) (ha : 0 < a) (hab : a ≤ b) :
    (uniqueOwnerLocalDeltaThickM 576
        (selectedOccurrenceNormalizedOuterCanonicalDelta
          P Rside ambient outerCF) a b : ENNReal) *
        ((a / b : NNReal) : ENNReal) ≤
      max 1
        (2 * (27 * (576 : ENNReal) ^ 3) * sourceKT * d⁻¹) := by
  apply uniqueOwnerLocalDeltaThickM_576_mul_aspectRatio_le_of_deltaCoefficient
    (selectedOccurrenceNormalizedOuterCanonicalDelta
      P Rside ambient outerCF) a b sourceKT d ha hab
  exact
    selectedOccurrenceNormalizedOuterCanonicalDelta_le_two_mul_sourceKT_mul_densityInverse_exactRside
      P Rside ambient sourceKT V d sourceCF outerCF hsourceKTTop
      hV hV0 hVTop hd0 hdTop hB0 hBTop hsourceCF houterCF

/-- Direct powered coupled loss for the canonical exact-`Rside` coefficient,
with the precise aspect-ratio spelling consumed by Equation (45). -/
theorem selectedOccurrenceCanonicalThickM_576_mul_ennrealAspectRatio_rpow_le_exactRside
    (Rside : Finset (Fin (blocks fine.bodyFamily P).length))
    (ambient : ConvexBody Space)
    (sourceKT V d sourceCF outerCF : ENNReal)
    (hsourceKTTop : sourceKT ≠ ∞)
    (hV : V = volume (ambient : Set Space))
    (hV0 : V ≠ 0) (hVTop : V ≠ ∞)
    (hd0 : d ≠ 0) (hdTop : d ≠ ∞)
    (hB0 : prop51SubselectedBodyVolume P Rside ≠ 0)
    (hBTop : prop51SubselectedBodyVolume P Rside ≠ ∞)
    (hsourceCF : sourceCF = sourceKT * V * d⁻¹ *
      (prop51SubselectedBodyVolume P Rside)⁻¹)
    (houterCF : outerCF = sourceCF * (2 * d) * d⁻¹)
    (a b : NNReal) (beta : Real)
    (ha : 0 < a) (hab : a ≤ b) (hbeta : 0 ≤ beta) :
    (((uniqueOwnerLocalDeltaThickM 576
        (selectedOccurrenceNormalizedOuterCanonicalDelta
          P Rside ambient outerCF) a b : ENNReal) *
        ((a : ENNReal) / (b : ENNReal))) ^ (beta / 2)) ≤
      (max 1
        (2 * (27 * (576 : ENNReal) ^ 3) * sourceKT * d⁻¹)) ^
          (beta / 2) := by
  apply
    uniqueOwnerLocalDeltaThickM_576_mul_ennrealAspectRatio_rpow_le_of_deltaCoefficient
      (selectedOccurrenceNormalizedOuterCanonicalDelta
        P Rside ambient outerCF) a b sourceKT d beta ha hab hbeta
  exact
    selectedOccurrenceNormalizedOuterCanonicalDelta_le_two_mul_sourceKT_mul_densityInverse_exactRside
      P Rside ambient sourceKT V d sourceCF outerCF hsourceKTTop
      hV hV0 hVTop hd0 hdTop hB0 hBTop hsourceCF houterCF

#print axioms
  selectedOccurrenceNormalizedOuterCanonicalDelta_le_two_mul_sourceKT_mul_densityInverse_of_producer
#print axioms
  selectedOccurrenceNormalizedOuterCanonicalDelta_le_two_mul_sourceKT_mul_densityInverse_exactRside
#print axioms
  uniqueOwnerLocalDeltaThickM_576_mul_aspectRatio_le_of_deltaCoefficient
#print axioms
  uniqueOwnerLocalDeltaThickM_576_mul_ennrealAspectRatio_le_of_deltaCoefficient
#print axioms
  uniqueOwnerLocalDeltaThickM_576_mul_ennrealAspectRatio_rpow_le_of_deltaCoefficient
#print axioms
  selectedOccurrenceCanonicalThickM_576_mul_aspectRatio_le_exactRside
#print axioms
  selectedOccurrenceCanonicalThickM_576_mul_ennrealAspectRatio_rpow_le_exactRside

end

end Family8SelectedOccurrenceCanonicalDeltaThickAspectAdapterV1
