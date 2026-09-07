import Family8Grounding.Family8GreedyWinnerAutomaticJohnSideBucketV1
import Family8Grounding.Family8HonestEq45CoupledThickAspectComparisonV1
import Mathlib.Tactic

/-!
# Selected-occurrence normalized outer scale bridge

An occupied winner-side bucket controls its normalized short width only
relative to its dyadic long endpoint.  The hypotheses `Rside.Nonempty`,
`hlabel`, and `hdelta` alone give the sharp unconditional statement

`2 * delta / sideShapeUpper label 2 <= bucketShortA label`.

To replace the denominator by the fixed constant `576`, one genuinely also
needs the unit-ball support used by `winnerLongSide_le_576`.  That bound and
the factor-two dyadic band give `sideShapeUpper label 2 <= 1152`, hence

`delta / 576 <= bucketShortA label`.

The second half records the exact Equation (45) price of applying the outer
factor at `delta / 576`: it is the fixed loss `576^(epsilon/2)`.  The proof
keeps every division and real power inside positive finite `NNReal` scales,
so it does not use any illicit cancellation involving `0` or `infinity`.
-/

open Set MeasureTheory
open scoped ENNReal NNReal

namespace Family8SelectedOccurrenceNormalizedOuterScaleBridgeV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.Uniformity
open Family6AffinePlankAnalyticHypothesesStableV1
open Family8GreedyWinnerAutomaticJohnSideBucketV1
open Family8HonestEq45CoupledThickAspectComparisonV1
open Family8Prop66AOuterInnerProductAlgebraV1
open Family8SelectedParentJohnPlankSideWidthBridgeV7

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000

universe u

variable {delta : NNReal} {iota : Type u}
  [Fintype iota] [DecidableEq iota]
  {fine : UniformTubeFamily delta iota}
  {active : Finset iota}

variable
  (P : GreedyDensityPartition fine.bodyFamily
    (hullCandidates active) (hullContainer fine.bodyFamily) active)

/-- The scale statement available from occupancy and the common side label
alone.  This is the exact version which does not assume a global upper bound
for the winner hulls. -/
theorem selectedOccurrenceNormalizedOuter_two_mul_delta_div_longEndpoint_le_bucketShortA
    (hdelta : 0 < delta)
    (labelOuter : Fin 3 → Int)
    (Rside : Finset (Fin (blocks fine.bodyFamily P).length))
    (hRside : Rside.Nonempty)
    (hlabel : ∀ k, k ∈ Rside →
      sideShapeLabel (winnerLongSide P hdelta k) = labelOuter) :
    2 * delta / sideShapeUpper labelOuter 2 <=
      bucketShortA labelOuter := by
  obtain ⟨k, hk⟩ := hRside
  have hshort (j : Fin 3) :
      2 * delta <= sideShapeUpper labelOuter j := by
    have hband := sideShapeUpper_half_lt_and_le
      (winnerLongSide_pos P hdelta k) j
    calc
      2 * delta <= winnerLongSide P hdelta k j :=
        two_mul_delta_le_winnerLongSide P hdelta k j
      _ <= sideShapeUpper labelOuter j := by
        simpa only [hlabel k hk] using hband.2
  have hlongPos : 0 < sideShapeUpper labelOuter 2 :=
    sideShapeUpper_pos labelOuter 2
  by_cases h01 : sideShapeUpper labelOuter 0 <=
      sideShapeUpper labelOuter 1
  · simp only [bucketShortA, if_pos h01]
    apply (div_le_div_iff₀ hlongPos hlongPos).2
    exact mul_le_mul' (hshort 0) le_rfl
  · simp only [bucketShortA, if_neg h01]
    apply (div_le_div_iff₀ hlongPos hlongPos).2
    exact mul_le_mul' (hshort 1) le_rfl

/-- Under the actual unit-ball support hypothesis, an occupied normalized
winner bucket has short width at least `delta / 576`.

The extra support premise is essential: without any upper bound on the long
winner side, translating otherwise unit-sized tubes arbitrarily far apart
can make the long-normalization denominator arbitrarily large. -/
theorem selectedOccurrenceNormalizedOuter_delta_div_576_le_bucketShortA
    (hdelta : 0 < delta)
    (labelOuter : Fin 3 → Int)
    (Rside : Finset (Fin (blocks fine.bodyFamily P).length))
    (hRside : Rside.Nonempty)
    (hlabel : ∀ k, k ∈ Rside →
      sideShapeLabel (winnerLongSide P hdelta k) = labelOuter)
    (hfineContained : ∀ i ∈ active,
      (fine.tubes i).carrier ⊆ Metric.closedBall (0 : Space) 1) :
    delta / 576 ≤ bucketShortA labelOuter := by
  obtain ⟨k, hk⟩ := hRside
  have hshort (j : Fin 3) :
      2 * delta <= sideShapeUpper labelOuter j := by
    have hband := sideShapeUpper_half_lt_and_le
      (winnerLongSide_pos P hdelta k) j
    calc
      2 * delta <= winnerLongSide P hdelta k j :=
        two_mul_delta_le_winnerLongSide P hdelta k j
      _ <= sideShapeUpper labelOuter j := by
        simpa only [hlabel k hk] using hband.2
  have hlongBand := sideShapeUpper_half_lt_and_le
    (winnerLongSide_pos P hdelta k) (2 : Fin 3)
  have hlongDyadic :
      sideShapeUpper labelOuter 2 <=
        2 * winnerLongSide P hdelta k 2 := by
    have hraw :
        sideShapeUpper
            (sideShapeLabel (winnerLongSide P hdelta k)) 2 <=
          2 * winnerLongSide P hdelta k 2 := by
      nlinarith [hlongBand.1]
    simpa only [hlabel k hk] using hraw
  have hlongUpper : sideShapeUpper labelOuter 2 <= 1152 := by
    calc
      sideShapeUpper labelOuter 2 <=
          2 * winnerLongSide P hdelta k 2 := hlongDyadic
      _ <= 2 * 576 := by
        exact mul_le_mul' le_rfl (winnerLongSide_le_576
          P hdelta hfineContained k 2)
      _ = 1152 := by norm_num
  have hlongPos : 0 < sideShapeUpper labelOuter 2 :=
    sideShapeUpper_pos labelOuter 2
  by_cases h01 : sideShapeUpper labelOuter 0 <=
      sideShapeUpper labelOuter 1
  · simp only [bucketShortA, if_pos h01]
    apply (div_le_div_iff₀
      (by norm_num : (0 : NNReal) < 576) hlongPos).2
    calc
      delta * sideShapeUpper labelOuter 2 <= delta * 1152 :=
        mul_le_mul' le_rfl hlongUpper
      _ = (2 * delta) * 576 := by ring
      _ <= sideShapeUpper labelOuter 0 * 576 :=
        mul_le_mul' (hshort 0) le_rfl
  · simp only [bucketShortA, if_neg h01]
    apply (div_le_div_iff₀
      (by norm_num : (0 : NNReal) < 576) hlongPos).2
    calc
      delta * sideShapeUpper labelOuter 2 <= delta * 1152 :=
        mul_le_mul' le_rfl hlongUpper
      _ = (2 * delta) * 576 := by ring
      _ <= sideShapeUpper labelOuter 1 * 576 :=
        mul_le_mul' (hshort 1) le_rfl

/-! ## The fixed Equation (45) scale price -/

/-- Replacing `delta` by `delta / 576` in the Proposition 6.6(A) outer
factor costs exactly `576^(epsilon/2)`.

Only the scale term changes.  Positivity of `delta` and the numerical
denominator makes both NNReal ratios nonzero; all coerced NNReal values are
finite.  Thus the identity remains valid even when one of the unrelated
outer-factor terms (for example `CF`) is `0` or `infinity`. -/
theorem proposition66AOuterFactor_delta_div_576_eq_fixedScaleLoss_mul
    {delta a b : NNReal} {plankCount : Nat}
    {CF : ENNReal} {epsilon beta : Real}
    (hdelta : 0 < delta) (hepsilon : 0 <= epsilon) :
    proposition66AOuterFactor (delta / 576) a b
        plankCount CF epsilon beta =
      (576 : ENNReal) ^ (epsilon / 2) *
        proposition66AOuterFactor delta a b
          plankCount CF epsilon beta := by
  have h576 : (0 : NNReal) < 576 := by norm_num
  have hhalf : 0 <= epsilon / 2 := by linarith
  have hreverse :
      (((delta / 576 : NNReal) : ENNReal) ^ (-epsilon / 2)) =
        ((((576 : NNReal) / delta : NNReal) : ENNReal) ^
          (epsilon / 2)) := by
    rw [<- ENNReal.coe_rpow_of_ne_zero (div_pos hdelta h576).ne',
      <- ENNReal.coe_rpow_of_ne_zero (div_pos h576 hdelta).ne',
      ENNReal.coe_inj]
    rw [show -epsilon / 2 = -(epsilon / 2) by ring]
    rw [NNReal.rpow_neg, <- NNReal.inv_rpow, inv_div]
  have hquotient :
      ((((576 : NNReal) / delta : NNReal) : ENNReal) ^
          (epsilon / 2)) =
        (576 : ENNReal) ^ (epsilon / 2) *
          (delta : ENNReal) ^ (-epsilon / 2) := by
    rw [ENNReal.coe_div hdelta.ne',
      ENNReal.div_rpow_of_nonneg _ _ hhalf, div_eq_mul_inv,
      show -epsilon / 2 = -(epsilon / 2) by ring,
      ENNReal.rpow_neg]
    norm_num
  unfold proposition66AOuterFactor
  rw [hreverse, hquotient]
  ac_rfl

/-- Inequality-facing version of the exact fixed-scale identity. -/
theorem proposition66AOuterFactor_delta_div_576_le_fixedScaleLoss_mul
    {delta a b : NNReal} {plankCount : Nat}
    {CF : ENNReal} {epsilon beta : Real}
    (hdelta : 0 < delta) (hepsilon : 0 <= epsilon) :
    proposition66AOuterFactor (delta / 576) a b
        plankCount CF epsilon beta <=
      (576 : ENNReal) ^ (epsilon / 2) *
        proposition66AOuterFactor delta a b
          plankCount CF epsilon beta := by
  exact le_of_eq
    (proposition66AOuterFactor_delta_div_576_eq_fixedScaleLoss_mul
      hdelta hepsilon)

/-- Ready-to-compose Family 6 comparison at the selected normalized scale.
The only fixed normalization price is `576^(epsilon/2)`; the honest coupled
thick/aspect loss stays visible and is not absorbed. -/
theorem convexPlankFrostmanFactor_halfEpsilon_le_fixedScaleLoss_mul_coupledThickAspect_mul_outer
    {index : Type u} [Fintype index] [DecidableEq index]
    {delta a b : NNReal}
    (D : ShadedConvexPlankFamily index a b)
    (CF : ENNReal) (M : NNReal) {epsilon beta : Real}
    (hdelta : 0 < delta) (hdeltaA : delta / 576 <= a) (hab : a <= b)
    (hepsilon : 0 < epsilon) (hbeta : 0 <= beta) :
    convexPlankFrostmanFactor D (epsilon / 2) beta CF M <=
      (576 : ENNReal) ^ (epsilon / 2) *
        ((((M : ENNReal) * ((a : ENNReal) / (b : ENNReal))) ^
          (beta / 2)) *
          proposition66AOuterFactor delta a b
            (Fintype.card index) CF epsilon beta) := by
  calc
    convexPlankFrostmanFactor D (epsilon / 2) beta CF M <=
        (((M : ENNReal) * ((a : ENNReal) / (b : ENNReal))) ^
          (beta / 2)) *
          proposition66AOuterFactor (delta / 576) a b
            (Fintype.card index) CF epsilon beta :=
      convexPlankFrostmanFactor_halfEpsilon_le_coupledThickAspect_mul_proposition66AOuterFactor_div_576
        D CF M hdelta hdeltaA hab hepsilon hbeta
    _ = (576 : ENNReal) ^ (epsilon / 2) *
        ((((M : ENNReal) * ((a : ENNReal) / (b : ENNReal))) ^
          (beta / 2)) *
          proposition66AOuterFactor delta a b
            (Fintype.card index) CF epsilon beta) := by
      rw [proposition66AOuterFactor_delta_div_576_eq_fixedScaleLoss_mul
        hdelta hepsilon.le]
      ac_rfl

#print axioms
  selectedOccurrenceNormalizedOuter_two_mul_delta_div_longEndpoint_le_bucketShortA
#print axioms
  selectedOccurrenceNormalizedOuter_delta_div_576_le_bucketShortA
#print axioms
  proposition66AOuterFactor_delta_div_576_eq_fixedScaleLoss_mul
#print axioms
  proposition66AOuterFactor_delta_div_576_le_fixedScaleLoss_mul
#print axioms
  convexPlankFrostmanFactor_halfEpsilon_le_fixedScaleLoss_mul_coupledThickAspect_mul_outer

end

end Family8SelectedOccurrenceNormalizedOuterScaleBridgeV1
