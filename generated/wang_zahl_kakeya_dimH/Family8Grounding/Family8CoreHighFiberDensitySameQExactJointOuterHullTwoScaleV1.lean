import Family8Grounding.Family8ComparableRLocalKTWholeEq32ScalarV1
import Family8Grounding.Family8SelectedOccurrenceCanonicalDeltaThickAspectAdapterV1
import Family8Grounding.Family8SelectedOccurrenceOuterInnerScaleMismatchPowerV1
import Mathlib.Tactic

/-!
# Exact inverse-density joint payment with genuinely different side scales

The selected-occurrence outer bucket and the selected-parent inner bucket
come from different John constructions.  Their side labels must therefore
remain independent.  This file keeps the actual inner fibre count in the
joint scalar and uses the existing scale-mismatch bridge only after the
whole outer-times-inner product has been assembled.

No equality between the outer and inner labels is assumed.  In particular,
the local gate contains the literal

`Inner(delta, innerA, innerB, tubesPerPlank)`

rather than replacing it by a count-one factor.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8CoreHighFiberDensitySameQExactJointOuterHullTwoScaleV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.Uniformity
open Family8ComparableRLocalKTWholeEq32ScalarV1
open Family8Prop51SelectedFineBlockDensityNormalizedFrostmanV1
open Family8Prop66AFrostmanAspectGainAlgebraV1
open Family8Prop66AOuterInnerProductAlgebraV1
open Family8Prop66InnerScaleMismatchAbsorptionV1
open Family8SelectedOccurrenceCanonicalDeltaThickAspectAdapterV1
open Family8SelectedOccurrenceNormalizedCanonicalGlobalDeltaEq45ControlV1
open Family8SelectedOccurrenceOuterInnerScaleMismatchPowerV1
open Family8SelectedParentJohnPlankSideWidthBridgeV7

noncomputable section

/-! ## Whole-product consumers at two independent side scales -/

/-- The local John estimate with the actual inner count left intact.

Unlike the count-one sufficient adapter, this theorem does not split the
fibre cardinality or compare it with a separately chosen count.  The sole
joint premise already contains the actual two-scale outer-times-inner
product. -/
theorem
    outerBound_mul_localDensityGeometricScale_le_of_jointOuterHullReserve_twoScale_actualCount
    {delta outerA outerB innerA innerB : NNReal}
    {plankCount tubesPerPlank : Nat}
    {d outerBound geometricScale jacobian sourceDensity area johnLoss
      geometryLoss targetCF densityLoss : ENNReal}
    {epsilon beta : Real}
    (hJohn : d * geometricScale <=
      jacobian * (johnLoss * ((tubesPerPlank : ENNReal) * area)))
    (hJointOuterHull :
      johnLoss * (tubesPerPlank : ENNReal) * outerBound <=
        (sourceDensity * geometryLoss * densityLoss) *
          (proposition66AOuterFactor delta outerA outerB plankCount
              targetCF epsilon beta *
            proposition66AInnerFactor delta innerA innerB tubesPerPlank
              epsilon beta)) :
    outerBound * (d * geometricScale) <=
      (jacobian * (sourceDensity * area)) *
        ((geometryLoss * densityLoss) *
          (proposition66AOuterFactor delta outerA outerB plankCount
              targetCF epsilon beta *
            proposition66AInnerFactor delta innerA innerB tubesPerPlank
              epsilon beta)) := by
  calc
    outerBound * (d * geometricScale) <=
        outerBound *
          (jacobian *
            (johnLoss * ((tubesPerPlank : ENNReal) * area))) :=
      mul_le_mul' le_rfl hJohn
    _ = (jacobian * area) *
        (johnLoss * (tubesPerPlank : ENNReal) * outerBound) := by
      ac_rfl
    _ <= (jacobian * area) *
        ((sourceDensity * geometryLoss * densityLoss) *
          (proposition66AOuterFactor delta outerA outerB plankCount
              targetCF epsilon beta *
            proposition66AInnerFactor delta innerA innerB tubesPerPlank
              epsilon beta)) :=
      mul_le_mul' le_rfl hJointOuterHull
    _ = (jacobian * (sourceDensity * area)) *
        ((geometryLoss * densityLoss) *
          (proposition66AOuterFactor delta outerA outerB plankCount
              targetCF epsilon beta *
            proposition66AInnerFactor delta innerA innerB tubesPerPlank
              epsilon beta)) := by
      ac_rfl

/-- Terminal whole-product cancellation at independent outer and inner
side scales.  The only scale transport is the existing exact mismatch
product theorem, and its loss remains explicit. -/
theorem
    average_le_wholeProp66AFrostmanFactor_of_jointOuterHullReserve_twoScale_actualCount
    {delta outerA outerB innerA innerB : NNReal}
    {plankCount tubesPerPlank totalCount : Nat}
    {average d outerBound geometricScale jacobian sourceDensity area johnLoss
      rawLoss geometryLoss targetCF densityLoss countLoss : ENNReal}
    {epsilon beta : Real}
    (hdelta : 0 < delta)
    (houterA : 0 < outerA) (houterB : 0 < outerB)
    (hinnerA : 0 < innerA) (hinnerB : 0 < innerB)
    (hbeta0 : 0 <= beta) (hbetaOne : beta <= 1)
    (hsource0 : jacobian * (sourceDensity * area) ≠ 0)
    (hsourceTop : jacobian * (sourceDensity * area) ≠ ∞)
    (hcount : ((plankCount * tubesPerPlank : Nat) : ENNReal) <=
      countLoss * (totalCount : ENNReal))
    (hscaled : (jacobian * (sourceDensity * area)) * average <=
      rawLoss * (outerBound * (d * geometricScale)))
    (hJohn : d * geometricScale <=
      jacobian * (johnLoss * ((tubesPerPlank : ENNReal) * area)))
    (hJointOuterHull :
      johnLoss * (tubesPerPlank : ENNReal) * outerBound <=
        (sourceDensity * geometryLoss * densityLoss) *
          (proposition66AOuterFactor delta outerA outerB plankCount
              targetCF epsilon beta *
            proposition66AInnerFactor delta innerA innerB tubesPerPlank
              epsilon beta)) :
    average <=
      (rawLoss * geometryLoss * densityLoss *
          (prop66InnerScaleMismatchLoss
              outerA outerB innerA innerB beta *
            countLoss ^ (1 - beta / 2))) *
        proposition66AFrostmanFactor delta outerA outerB totalCount
          targetCF epsilon beta := by
  have hlocal :=
    outerBound_mul_localDensityGeometricScale_le_of_jointOuterHullReserve_twoScale_actualCount
      hJohn hJointOuterHull
  have hcountPayment :=
    proposition66AOuterFactor_mul_innerFactor_le_innerScaleMismatch_countLoss_mul_frostmanFactor
      (CF := targetCF) (countLoss := countLoss)
      (epsilon := epsilon) (beta := beta)
      hdelta houterA houterB hinnerA hinnerB hbeta0 hbetaOne hcount
  apply (ENNReal.mul_le_mul_iff_left hsource0 hsourceTop).mp
  calc
    average * (jacobian * (sourceDensity * area)) =
        (jacobian * (sourceDensity * area)) * average := by
      ac_rfl
    _ <= rawLoss * (outerBound * (d * geometricScale)) := hscaled
    _ <= rawLoss *
        ((jacobian * (sourceDensity * area)) *
          ((geometryLoss * densityLoss) *
            (proposition66AOuterFactor delta outerA outerB plankCount
                targetCF epsilon beta *
              proposition66AInnerFactor delta innerA innerB tubesPerPlank
                epsilon beta))) :=
      mul_le_mul' le_rfl hlocal
    _ <= rawLoss *
        ((jacobian * (sourceDensity * area)) *
          ((geometryLoss * densityLoss) *
            ((prop66InnerScaleMismatchLoss
                outerA outerB innerA innerB beta *
              countLoss ^ (1 - beta / 2)) *
                proposition66AFrostmanFactor delta outerA outerB totalCount
                  targetCF epsilon beta))) :=
      mul_le_mul' le_rfl
        (mul_le_mul' le_rfl (mul_le_mul' le_rfl hcountPayment))
    _ = ((rawLoss * geometryLoss * densityLoss *
          (prop66InnerScaleMismatchLoss
              outerA outerB innerA innerB beta *
            countLoss ^ (1 - beta / 2))) *
        proposition66AFrostmanFactor delta outerA outerB totalCount
          targetCF epsilon beta) *
          (jacobian * (sourceDensity * area)) := by
      ac_rfl

/-- A consumer-facing form where an externally proved upper bound for the
scale mismatch is substituted only after the exact mismatch bridge. -/
theorem
    average_le_wholeProp66AFrostmanFactor_of_jointOuterHullReserve_twoScale_actualCount_of_mismatchBound
    {delta outerA outerB innerA innerB : NNReal}
    {plankCount tubesPerPlank totalCount : Nat}
    {average d outerBound geometricScale jacobian sourceDensity area johnLoss
      rawLoss geometryLoss targetCF densityLoss countLoss mismatchBound : ENNReal}
    {epsilon beta : Real}
    (hdelta : 0 < delta)
    (houterA : 0 < outerA) (houterB : 0 < outerB)
    (hinnerA : 0 < innerA) (hinnerB : 0 < innerB)
    (hbeta0 : 0 <= beta) (hbetaOne : beta <= 1)
    (hsource0 : jacobian * (sourceDensity * area) ≠ 0)
    (hsourceTop : jacobian * (sourceDensity * area) ≠ ∞)
    (hcount : ((plankCount * tubesPerPlank : Nat) : ENNReal) <=
      countLoss * (totalCount : ENNReal))
    (hMismatch : prop66InnerScaleMismatchLoss
      outerA outerB innerA innerB beta <= mismatchBound)
    (hscaled : (jacobian * (sourceDensity * area)) * average <=
      rawLoss * (outerBound * (d * geometricScale)))
    (hJohn : d * geometricScale <=
      jacobian * (johnLoss * ((tubesPerPlank : ENNReal) * area)))
    (hJointOuterHull :
      johnLoss * (tubesPerPlank : ENNReal) * outerBound <=
        (sourceDensity * geometryLoss * densityLoss) *
          (proposition66AOuterFactor delta outerA outerB plankCount
              targetCF epsilon beta *
            proposition66AInnerFactor delta innerA innerB tubesPerPlank
              epsilon beta)) :
    average <=
      (rawLoss * geometryLoss * densityLoss *
          (mismatchBound * countLoss ^ (1 - beta / 2))) *
        proposition66AFrostmanFactor delta outerA outerB totalCount
          targetCF epsilon beta := by
  have hbase :=
    average_le_wholeProp66AFrostmanFactor_of_jointOuterHullReserve_twoScale_actualCount
      hdelta houterA houterB hinnerA hinnerB hbeta0 hbetaOne
      hsource0 hsourceTop hcount hscaled hJohn hJointOuterHull
  calc
    average <=
        (rawLoss * geometryLoss * densityLoss *
            (prop66InnerScaleMismatchLoss
                outerA outerB innerA innerB beta *
              countLoss ^ (1 - beta / 2))) *
          proposition66AFrostmanFactor delta outerA outerB totalCount
            targetCF epsilon beta := hbase
    _ <= (rawLoss * geometryLoss * densityLoss *
          (mismatchBound * countLoss ^ (1 - beta / 2))) *
        proposition66AFrostmanFactor delta outerA outerB totalCount
          targetCF epsilon beta :=
      mul_le_mul'
        (mul_le_mul' le_rfl (mul_le_mul' hMismatch le_rfl)) le_rfl

/-- The abstract two-label relation supplies the mismatch upper bound
without identifying the labels.  The actual selected-occurrence theorem
constructs this relation with floors `deltaOuter / 576` and
`rho / 11943936`. -/
theorem
    average_le_wholeProp66AFrostmanFactor_of_jointOuterHullReserve_twoLabels_actualCount
    {delta outerFloor innerFloor : NNReal}
    {labelOuter labelInner : Fin 3 -> Int}
    {plankCount tubesPerPlank totalCount : Nat}
    {average d outerBound geometricScale jacobian sourceDensity area johnLoss
      rawLoss geometryLoss targetCF densityLoss countLoss : ENNReal}
    {epsilon beta : Real}
    (hrel : Prop66OuterInnerLabelScaleRelation
      outerFloor innerFloor labelOuter labelInner)
    (hdelta : 0 < delta)
    (hbeta0 : 0 <= beta) (hbetaOne : beta <= 1)
    (hsource0 : jacobian * (sourceDensity * area) ≠ 0)
    (hsourceTop : jacobian * (sourceDensity * area) ≠ ∞)
    (hcount : ((plankCount * tubesPerPlank : Nat) : ENNReal) <=
      countLoss * (totalCount : ENNReal))
    (hscaled : (jacobian * (sourceDensity * area)) * average <=
      rawLoss * (outerBound * (d * geometricScale)))
    (hJohn : d * geometricScale <=
      jacobian * (johnLoss * ((tubesPerPlank : ENNReal) * area)))
    (hJointOuterHull :
      johnLoss * (tubesPerPlank : ENNReal) * outerBound <=
        (sourceDensity * geometryLoss * densityLoss) *
          (proposition66AOuterFactor delta
              (bucketShortA labelOuter) (bucketShortB labelOuter)
              plankCount targetCF epsilon beta *
            proposition66AInnerFactor delta
              (bucketShortA labelInner) (bucketShortB labelInner)
              tubesPerPlank epsilon beta)) :
    average <=
      (rawLoss * geometryLoss * densityLoss *
          (((outerFloor : ENNReal) ^ (-beta) *
              (innerFloor : ENNReal) ^ (2 * beta - 2)) *
            countLoss ^ (1 - beta / 2))) *
        proposition66AFrostmanFactor delta
          (bucketShortA labelOuter) (bucketShortB labelOuter)
          totalCount targetCF epsilon beta := by
  have houterA : 0 < bucketShortA labelOuter :=
    hrel.outerFloor_pos.trans_le hrel.outerFloor_le_shortA
  have houterB : 0 < bucketShortB labelOuter :=
    houterA.trans_le (bucketShortA_le_bucketShortB labelOuter)
  have hinnerA : 0 < bucketShortA labelInner :=
    hrel.innerFloor_pos.trans_le hrel.innerFloor_le_shortA
  have hinnerB : 0 < bucketShortB labelInner :=
    hinnerA.trans_le (bucketShortA_le_bucketShortB labelInner)
  exact
    average_le_wholeProp66AFrostmanFactor_of_jointOuterHullReserve_twoScale_actualCount_of_mismatchBound
      hdelta houterA houterB hinnerA hinnerB hbeta0 hbetaOne
      hsource0 hsourceTop hcount
      (hrel.innerMismatchLoss_le hbeta0 hbetaOne)
      hscaled hJohn hJointOuterHull

/-! ## Exact inverse-density producer with the actual inner count -/

/-- Exact inverse-density lifting for genuinely independent outer and inner
side scales.  The inverse-density exponent is retained, while the actual
inner count and its actual inner side pair pass through unchanged. -/
theorem jointOuterHullReserve_twoScale_actualCount_of_inverseDensityOuterCF
    {delta outerA outerB innerA innerB : NNReal}
    {plankCount tubesPerPlank : Nat}
    {d0 coefficientLoss outerCF sourceCF refinementLoss johnLoss
      sourceDensity geometryLoss : ENNReal}
    {epsilon beta : Real}
    (hbetaOne : beta <= 1)
    (houterCF : outerCF <= coefficientLoss * sourceCF * d0⁻¹)
    (hscalar :
      johnLoss * (tubesPerPlank : ENNReal) *
          d0 ^ (-(1 - beta / 2)) <=
        (sourceDensity * geometryLoss) *
          proposition66AInnerFactor delta innerA innerB tubesPerPlank
            epsilon beta) :
    johnLoss * (tubesPerPlank : ENNReal) *
        proposition66AOuterFactor delta outerA outerB plankCount
          (outerCF * refinementLoss) epsilon beta <=
      (sourceDensity * geometryLoss *
          coefficientLoss ^ (1 - beta / 2)) *
        (proposition66AOuterFactor delta outerA outerB plankCount
            (sourceCF * refinementLoss) epsilon beta *
          proposition66AInnerFactor delta innerA innerB tubesPerPlank
            epsilon beta) := by
  let p : Real := 1 - beta / 2
  have hp : 0 <= p := by
    dsimp only [p]
    linarith
  have hCF : outerCF * refinementLoss <=
      coefficientLoss * (sourceCF * refinementLoss) * d0⁻¹ := by
    calc
      outerCF * refinementLoss <=
          (coefficientLoss * sourceCF * d0⁻¹) * refinementLoss :=
        mul_le_mul' houterCF le_rfl
      _ = coefficientLoss * (sourceCF * refinementLoss) * d0⁻¹ := by
        ac_rfl
  have hCFpow : (outerCF * refinementLoss) ^ p <=
      coefficientLoss ^ p * (sourceCF * refinementLoss) ^ p *
        d0 ^ (-p) := by
    calc
      (outerCF * refinementLoss) ^ p <=
          (coefficientLoss * (sourceCF * refinementLoss) * d0⁻¹) ^ p :=
        ENNReal.rpow_le_rpow hCF hp
      _ = coefficientLoss ^ p * (sourceCF * refinementLoss) ^ p *
          d0 ^ (-p) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ hp,
          ENNReal.mul_rpow_of_nonneg _ _ hp,
          ENNReal.inv_rpow, <- ENNReal.rpow_neg]
  rw [proposition66AOuterFactor_eq_CF_rpow_mul_independent,
    proposition66AOuterFactor_eq_CF_rpow_mul_independent]
  calc
    johnLoss * (tubesPerPlank : ENNReal) *
        ((outerCF * refinementLoss) ^ (1 - beta / 2) *
          proposition66AOuterCFIndependentFactor
            delta outerA outerB plankCount epsilon beta) <=
      johnLoss * (tubesPerPlank : ENNReal) *
        ((coefficientLoss ^ p *
            (sourceCF * refinementLoss) ^ p * d0 ^ (-p)) *
          proposition66AOuterCFIndependentFactor
            delta outerA outerB plankCount epsilon beta) :=
      mul_le_mul' le_rfl (mul_le_mul' (by
        simpa only [p] using hCFpow) le_rfl)
    _ = (johnLoss * (tubesPerPlank : ENNReal) *
          d0 ^ (-(1 - beta / 2))) *
        (coefficientLoss ^ (1 - beta / 2) *
          ((sourceCF * refinementLoss) ^ (1 - beta / 2) *
            proposition66AOuterCFIndependentFactor
              delta outerA outerB plankCount epsilon beta)) := by
      dsimp only [p]
      ac_rfl
    _ <= ((sourceDensity * geometryLoss) *
          proposition66AInnerFactor delta innerA innerB tubesPerPlank
            epsilon beta) *
        (coefficientLoss ^ (1 - beta / 2) *
          ((sourceCF * refinementLoss) ^ (1 - beta / 2) *
            proposition66AOuterCFIndependentFactor
              delta outerA outerB plankCount epsilon beta)) :=
      mul_le_mul' hscalar le_rfl
    _ = (sourceDensity * geometryLoss *
          coefficientLoss ^ (1 - beta / 2)) *
        (((sourceCF * refinementLoss) ^ (1 - beta / 2) *
            proposition66AOuterCFIndependentFactor
              delta outerA outerB plankCount epsilon beta) *
          proposition66AInnerFactor delta innerA innerB tubesPerPlank
            epsilon beta) := by
      ac_rfl

universe u

variable {delta : NNReal} {iota : Type u}
  [Fintype iota] [DecidableEq iota]
  {fine : UniformTubeFamily delta iota}
  {active : Finset iota}

variable
  (P : GreedyDensityPartition fine.bodyFamily
    (hullCandidates active) (hullContainer fine.bodyFamily) active)

/-- Same-`Rside` V552 specialization of the two-scale actual-count
producer.  The outer and inner side pairs are independent parameters; the
theorem neither chooses nor equates their labels. -/
theorem
    selectedOccurrenceCanonicalDelta_jointOuterHullReserve_exactRside_twoScale_actualCount
    (Rside : Finset (Fin (blocks fine.bodyFamily P).length))
    (ambient : ConvexBody Space)
    (sourceKT V d sourceCF rawOuterCF refinementLoss johnLoss
      sourceDensity geometryLoss : ENNReal)
    (hsourceKTTop : sourceKT ≠ ∞)
    (hV : V = volume (ambient : Set Space))
    (hV0 : V ≠ 0) (hVTop : V ≠ ∞)
    (hd0 : d ≠ 0) (hdTop : d ≠ ∞)
    (hB0 : prop51SubselectedBodyVolume P Rside ≠ 0)
    (hBTop : prop51SubselectedBodyVolume P Rside ≠ ∞)
    (hsourceCF : sourceCF = sourceKT * V * d⁻¹ *
      (prop51SubselectedBodyVolume P Rside)⁻¹)
    (hrawOuterCF : rawOuterCF = sourceCF * (2 * d) * d⁻¹)
    (outerA outerB innerA innerB : NNReal)
    (plankCount tubesPerPlank : Nat)
    (epsilon beta : Real) (hbetaOne : beta <= 1)
    (hscalar :
      johnLoss * (tubesPerPlank : ENNReal) *
          d ^ (-(1 - beta / 2)) <=
        (sourceDensity * geometryLoss) *
          proposition66AInnerFactor delta innerA innerB tubesPerPlank
            epsilon beta) :
    johnLoss * (tubesPerPlank : ENNReal) *
        proposition66AOuterFactor delta outerA outerB plankCount
          (((selectedOccurrenceNormalizedOuterCanonicalDelta
              P Rside ambient rawOuterCF : NNReal) : ENNReal) *
            refinementLoss) epsilon beta <=
      (sourceDensity * geometryLoss *
          (2 : ENNReal) ^ (1 - beta / 2)) *
        (proposition66AOuterFactor delta outerA outerB plankCount
            (sourceKT * refinementLoss) epsilon beta *
          proposition66AInnerFactor delta innerA innerB tubesPerPlank
            epsilon beta) := by
  have hDelta :=
    selectedOccurrenceNormalizedOuterCanonicalDelta_le_two_mul_sourceKT_mul_densityInverse_exactRside
      P Rside ambient sourceKT V d sourceCF rawOuterCF hsourceKTTop hV
        hV0 hVTop hd0 hdTop hB0 hBTop hsourceCF hrawOuterCF
  exact
    jointOuterHullReserve_twoScale_actualCount_of_inverseDensityOuterCF
      (delta := delta) (outerA := outerA) (outerB := outerB)
      (innerA := innerA) (innerB := innerB)
      (plankCount := plankCount) (tubesPerPlank := tubesPerPlank)
      (d0 := d) (coefficientLoss := 2)
      (outerCF :=
        (selectedOccurrenceNormalizedOuterCanonicalDelta
          P Rside ambient rawOuterCF : NNReal))
      (sourceCF := sourceKT) (refinementLoss := refinementLoss)
      (johnLoss := johnLoss) (sourceDensity := sourceDensity)
      (geometryLoss := geometryLoss) (epsilon := epsilon) (beta := beta)
      hbetaOne (by simpa only using hDelta) hscalar

#print axioms
  outerBound_mul_localDensityGeometricScale_le_of_jointOuterHullReserve_twoScale_actualCount
#print axioms
  average_le_wholeProp66AFrostmanFactor_of_jointOuterHullReserve_twoScale_actualCount
#print axioms
  average_le_wholeProp66AFrostmanFactor_of_jointOuterHullReserve_twoScale_actualCount_of_mismatchBound
#print axioms
  average_le_wholeProp66AFrostmanFactor_of_jointOuterHullReserve_twoLabels_actualCount
#print axioms
  jointOuterHullReserve_twoScale_actualCount_of_inverseDensityOuterCF
#print axioms
  selectedOccurrenceCanonicalDelta_jointOuterHullReserve_exactRside_twoScale_actualCount

end
end Family8CoreHighFiberDensitySameQExactJointOuterHullTwoScaleV1
