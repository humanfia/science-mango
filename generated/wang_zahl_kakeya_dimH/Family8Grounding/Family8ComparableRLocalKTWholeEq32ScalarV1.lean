import Family8Grounding.Family8Prop66AUniformCountLossAlgebraV3
import Mathlib.Tactic

/-!
# Comparable-R local-density payment for the whole Proposition 6.6(A) product

This file records the scalar seam needed after the V552--V557 comparable-`R`
construction.  The local Cordoba estimate is allowed to contain the literal
block density `d`.  It is never bounded independently by the inner
Proposition 6.6(A) factor.

Instead, `d = d^(beta/2) * d^(1-beta/2)` is paid jointly:

* `d^(beta/2)` is absorbed together with the outer Frostman coefficient;
* `d^(1-beta/2)` is absorbed by the fibre count;
* the remaining, count-free inner scale is exposed as one honest geometric
  premise.

Thus the module discharges the density and comparable-`R` count bookkeeping
without introducing a stronger standalone Equation (46) assertion.
-/

open scoped ENNReal NNReal

namespace Family8ComparableRLocalKTWholeEq32ScalarV1

open Family8Prop66AFrostmanAspectGainAlgebraV1
open Family8Prop66AOuterInnerProductAlgebraV1
open Family8Prop66AUniformCountLossAlgebraV3

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

/-- The part of Equation (45) which is independent of the Frostman
coefficient. -/
def proposition66AOuterCFIndependentFactor
    (delta a b : NNReal) (plankCount : Nat)
    (epsilon beta : Real) : ENNReal :=
  (delta : ENNReal) ^ (-epsilon / 2) *
    ((a : ENNReal) / (b : ENNReal)) ^ (1 - beta / 2) *
      (b : ENNReal) ^ (-2 * beta) *
        (((b : ENNReal) ^ (2 : Nat)) *
          (plankCount : ENNReal)) ^ (1 - beta / 2)

/-- Equation (45) is its coefficient power times the coefficient-free
factor. -/
theorem proposition66AOuterFactor_eq_CF_rpow_mul_independent
    (delta a b : NNReal) (plankCount : Nat)
    (CF : ENNReal) (epsilon beta : Real) :
    proposition66AOuterFactor delta a b plankCount CF epsilon beta =
      CF ^ (1 - beta / 2) *
        proposition66AOuterCFIndependentFactor
          delta a b plankCount epsilon beta := by
  unfold proposition66AOuterFactor proposition66AOuterCFIndependentFactor
  ac_rfl

/-- A joint density/Frostman comparison lifts verbatim to the complete
Equation (45) factor. -/
theorem localDensityResidual_mul_outerFactor_le
    {delta a b : NNReal} {plankCount : Nat}
    {d CF targetCF densityLoss : ENNReal} {epsilon beta : Real}
    (hjoint :
      d ^ (beta / 2) * CF ^ (1 - beta / 2) <=
        densityLoss * targetCF ^ (1 - beta / 2)) :
    d ^ (beta / 2) *
        proposition66AOuterFactor delta a b plankCount CF epsilon beta <=
      densityLoss *
        proposition66AOuterFactor
          delta a b plankCount targetCF epsilon beta := by
  rw [proposition66AOuterFactor_eq_CF_rpow_mul_independent,
    proposition66AOuterFactor_eq_CF_rpow_mul_independent]
  calc
    d ^ (beta / 2) *
        (CF ^ (1 - beta / 2) *
          proposition66AOuterCFIndependentFactor
            delta a b plankCount epsilon beta) =
      (d ^ (beta / 2) * CF ^ (1 - beta / 2)) *
        proposition66AOuterCFIndependentFactor
          delta a b plankCount epsilon beta := by
      ac_rfl
    _ <= (densityLoss * targetCF ^ (1 - beta / 2)) *
        proposition66AOuterCFIndependentFactor
          delta a b plankCount epsilon beta :=
      mul_le_mul' hjoint le_rfl
    _ = densityLoss *
        (targetCF ^ (1 - beta / 2) *
          proposition66AOuterCFIndependentFactor
            delta a b plankCount epsilon beta) := by
      ac_rfl

/-- General form of the preceding lifting when Equation (45) carries an
additional honest thickening/aspect factor.  In the exact-R application
the inverse density may live in this auxiliary factor rather than in CF;
the joint premise therefore keeps their product literal and prevents a
duplicate inverse-density payment. -/
theorem localDensityResidual_mul_outerAux_mul_outerFactor_le
    {delta a b : NNReal} {plankCount : Nat}
    {d outerAux CF targetCF densityLoss : ENNReal} {epsilon beta : Real}
    (hjoint :
      d ^ (beta / 2) * outerAux * CF ^ (1 - beta / 2) <=
        densityLoss * targetCF ^ (1 - beta / 2)) :
    d ^ (beta / 2) *
        (outerAux *
          proposition66AOuterFactor delta a b plankCount CF epsilon beta) <=
      densityLoss *
        proposition66AOuterFactor
          delta a b plankCount targetCF epsilon beta := by
  rw [proposition66AOuterFactor_eq_CF_rpow_mul_independent,
    proposition66AOuterFactor_eq_CF_rpow_mul_independent]
  calc
    d ^ (beta / 2) *
        (outerAux *
          (CF ^ (1 - beta / 2) *
            proposition66AOuterCFIndependentFactor
              delta a b plankCount epsilon beta)) =
      (d ^ (beta / 2) * outerAux * CF ^ (1 - beta / 2)) *
        proposition66AOuterCFIndependentFactor
          delta a b plankCount epsilon beta := by
      ac_rfl
    _ <= (densityLoss * targetCF ^ (1 - beta / 2)) *
        proposition66AOuterCFIndependentFactor
          delta a b plankCount epsilon beta :=
      mul_le_mul' hjoint le_rfl
    _ = densityLoss *
        (targetCF ^ (1 - beta / 2) *
          proposition66AOuterCFIndependentFactor
            delta a b plankCount epsilon beta) := by
      ac_rfl

/-- The tube-count dependence of Equation (46) is exactly
`tubesPerPlank^(1-beta/2)`.  The factor with count one is the honest
count-free geometric scale used below. -/
theorem proposition66AInnerFactor_eq_countOne_mul_card_rpow
    (delta a b : NNReal) (tubesPerPlank : Nat)
    (epsilon beta : Real) (hbetaOne : beta <= 1) :
    proposition66AInnerFactor delta a b tubesPerPlank epsilon beta =
      proposition66AInnerFactor delta a b 1 epsilon beta *
        (tubesPerPlank : ENNReal) ^ (1 - beta / 2) := by
  have hp : 0 <= 1 - beta / 2 := by linarith
  unfold proposition66AInnerFactor
  rw [ENNReal.mul_rpow_of_nonneg _ _ hp]
  simp only [Nat.cast_one, mul_one]
  ac_rfl

/-- Whole outer-times-inner payment for a local Cordoba coefficient.

The two premises are the weakest joint outer and inner gates.  In particular,
the inner gate retains the literal `tubesPerPlank`; a count-one geometric
reserve is only one optional sufficient producer recorded below. -/
theorem outerBound_mul_localDensityGeometricScale_le_jointProp66AProduct
    {delta a b : NNReal} {plankCount tubesPerPlank : Nat}
    {d outerBound geometricScale sourceFactor geometryLoss targetCF
      densityLoss : ENNReal}
    {epsilon beta : Real}
    (hd0 : d ≠ 0) (hdTop : d ≠ ∞)
    (houterJoint :
      d ^ (beta / 2) * outerBound <=
        densityLoss *
          proposition66AOuterFactor
            delta a b plankCount targetCF epsilon beta)
    (hinnerJoint :
      d ^ (1 - beta / 2) * geometricScale <=
        (sourceFactor * geometryLoss) *
          proposition66AInnerFactor
            delta a b tubesPerPlank epsilon beta) :
    outerBound * (d * geometricScale) <=
      (sourceFactor * geometryLoss * densityLoss) *
        (proposition66AOuterFactor
            delta a b plankCount targetCF epsilon beta *
          proposition66AInnerFactor
            delta a b tubesPerPlank epsilon beta) := by
  have hdSplit : d = d ^ (beta / 2) * d ^ (1 - beta / 2) := by
    calc
      d = d ^ (1 : Real) := (ENNReal.rpow_one d).symm
      _ = d ^ ((beta / 2) + (1 - beta / 2)) := by
        congr 1
        ring
      _ = d ^ (beta / 2) * d ^ (1 - beta / 2) := by
        rw [ENNReal.rpow_add _ _ hd0 hdTop]
  have hdSplitMul : d * geometricScale =
      (d ^ (beta / 2) * d ^ (1 - beta / 2)) * geometricScale :=
    congrArg (fun x : ENNReal => x * geometricScale) hdSplit
  calc
    outerBound * (d * geometricScale) =
      (d ^ (beta / 2) * outerBound) *
        (d ^ (1 - beta / 2) * geometricScale) := by
      rw [hdSplitMul]
      ac_rfl
    _ <= (densityLoss *
          proposition66AOuterFactor
            delta a b plankCount targetCF epsilon beta) *
        ((sourceFactor * geometryLoss) *
          proposition66AInnerFactor
            delta a b tubesPerPlank epsilon beta) :=
      mul_le_mul' houterJoint hinnerJoint
    _ = (sourceFactor * geometryLoss * densityLoss) *
        (proposition66AOuterFactor
            delta a b plankCount targetCF epsilon beta *
          proposition66AInnerFactor
            delta a b tubesPerPlank epsilon beta) := by
      ac_rfl

/-- A convenient sufficient producer for the inner joint gate.  It is kept
separate from the weakest core above: callers with sharper geometry or a
different density/count coupling can provide the joint gate directly. -/
theorem localDensityInnerJoint_of_countOne
    {delta a b : NNReal} {tubesPerPlank : Nat}
    {d geometricScale sourceFactor geometryLoss : ENNReal}
    {epsilon beta : Real}
    (hbetaOne : beta <= 1)
    (hdcard : d <= (tubesPerPlank : ENNReal))
    (hgeometry : geometricScale <=
      sourceFactor * geometryLoss *
        proposition66AInnerFactor delta a b 1 epsilon beta) :
    d ^ (1 - beta / 2) * geometricScale <=
      (sourceFactor * geometryLoss) *
        proposition66AInnerFactor
          delta a b tubesPerPlank epsilon beta := by
  have hp : 0 <= 1 - beta / 2 := by linarith
  have hdpow : d ^ (1 - beta / 2) <=
      (tubesPerPlank : ENNReal) ^ (1 - beta / 2) :=
    ENNReal.rpow_le_rpow hdcard hp
  have hinnerCount :=
    proposition66AInnerFactor_eq_countOne_mul_card_rpow
      delta a b tubesPerPlank epsilon beta hbetaOne
  calc
    d ^ (1 - beta / 2) * geometricScale <=
        (tubesPerPlank : ENNReal) ^ (1 - beta / 2) *
          (sourceFactor * geometryLoss *
            proposition66AInnerFactor delta a b 1 epsilon beta) :=
      mul_le_mul' hdpow hgeometry
    _ = (sourceFactor * geometryLoss) *
        (proposition66AInnerFactor delta a b 1 epsilon beta *
          (tubesPerPlank : ENNReal) ^ (1 - beta / 2)) := by
      ac_rfl
    _ = (sourceFactor * geometryLoss) *
        proposition66AInnerFactor
          delta a b tubesPerPlank epsilon beta := by
      rw [<- hinnerCount]

/-- Count-one geometric reserve plus d <= fibre-card implies the weakest
whole-product core. -/
theorem
    outerBound_mul_localDensityGeometricScale_le_jointProp66AProduct_of_countOne
    {delta a b : NNReal} {plankCount tubesPerPlank : Nat}
    {d outerBound geometricScale sourceFactor geometryLoss targetCF
      densityLoss : ENNReal}
    {epsilon beta : Real}
    (hbetaOne : beta <= 1)
    (hd0 : d ≠ 0) (hdTop : d ≠ ∞)
    (hdcard : d <= (tubesPerPlank : ENNReal))
    (hgeometry : geometricScale <=
      sourceFactor * geometryLoss *
        proposition66AInnerFactor delta a b 1 epsilon beta)
    (houterJoint :
      d ^ (beta / 2) * outerBound <=
        densityLoss *
          proposition66AOuterFactor
            delta a b plankCount targetCF epsilon beta) :
    outerBound * (d * geometricScale) <=
      (sourceFactor * geometryLoss * densityLoss) *
        (proposition66AOuterFactor
            delta a b plankCount targetCF epsilon beta *
          proposition66AInnerFactor
            delta a b tubesPerPlank epsilon beta) := by
  apply outerBound_mul_localDensityGeometricScale_le_jointProp66AProduct
    hd0 hdTop houterJoint
  exact localDensityInnerJoint_of_countOne
    hbetaOne hdcard hgeometry

/-- Terminal cancellation and comparable-count adapter.

This is the form consumed by an endpoint proof after Equation (44), the
outer Equation (45) estimate, and the local positive-carrier Cordoba estimate
have been assembled into `hscaled`.  A bound such as
`Rside.card * B.card <= 2 * totalCount` is passed as `hcount` with
`countLoss = 2`. -/
theorem average_le_wholeProp66AFrostmanFactor_of_scaled_localDensity
    {delta a b : NNReal} {plankCount tubesPerPlank totalCount : Nat}
    {average d outerBound geometricScale sourceFactor rawLoss geometryLoss
      targetCF densityLoss countLoss : ENNReal}
    {epsilon beta : Real}
    (hdelta : 0 < delta) (ha : 0 < a) (hb : 0 < b)
    (hbeta0 : 0 <= beta) (hbetaOne : beta <= 1)
    (hsource0 : sourceFactor ≠ 0) (hsourceTop : sourceFactor ≠ ∞)
    (hd0 : d ≠ 0) (hdTop : d ≠ ∞)
    (hcount : ((plankCount * tubesPerPlank : Nat) : ENNReal) <=
      countLoss * (totalCount : ENNReal))
    (hscaled : sourceFactor * average <=
      rawLoss * (outerBound * (d * geometricScale)))
    (houterJoint :
      d ^ (beta / 2) * outerBound <=
        densityLoss *
          proposition66AOuterFactor
            delta a b plankCount targetCF epsilon beta)
    (hinnerJoint :
      d ^ (1 - beta / 2) * geometricScale <=
        (sourceFactor * geometryLoss) *
          proposition66AInnerFactor
            delta a b tubesPerPlank epsilon beta) :
    average <=
      (rawLoss * geometryLoss * densityLoss *
          countLoss ^ (1 - beta / 2)) *
        proposition66AFrostmanFactor
          delta a b totalCount targetCF epsilon beta := by
  have hlocal :=
    outerBound_mul_localDensityGeometricScale_le_jointProp66AProduct
      hd0 hdTop houterJoint hinnerJoint
  have hcountPayment :=
    proposition66AOuterFactor_mul_innerFactor_le_countLoss_mul_frostmanFactor
      (CF := targetCF) (countLoss := countLoss)
      (epsilon := epsilon) (beta := beta)
      hdelta ha hb hbeta0 hbetaOne hcount
  apply (ENNReal.mul_le_mul_iff_left hsource0 hsourceTop).mp
  calc
    average * sourceFactor = sourceFactor * average := by ac_rfl
    _ <= rawLoss * (outerBound * (d * geometricScale)) := hscaled
    _ <= rawLoss *
        ((sourceFactor * geometryLoss * densityLoss) *
          (proposition66AOuterFactor
              delta a b plankCount targetCF epsilon beta *
            proposition66AInnerFactor
              delta a b tubesPerPlank epsilon beta)) :=
      mul_le_mul' le_rfl hlocal
    _ <= rawLoss *
        ((sourceFactor * geometryLoss * densityLoss) *
          (countLoss ^ (1 - beta / 2) *
            proposition66AFrostmanFactor
              delta a b totalCount targetCF epsilon beta)) :=
      mul_le_mul' le_rfl (mul_le_mul' le_rfl hcountPayment)
    _ =
        ((rawLoss * geometryLoss * densityLoss *
            countLoss ^ (1 - beta / 2)) *
          proposition66AFrostmanFactor
            delta a b totalCount targetCF epsilon beta) * sourceFactor := by
      ac_rfl

/-- Sufficient terminal corollary using the elementary d <= fibre-card
payment and a count-one geometric reserve. -/
theorem
    average_le_wholeProp66AFrostmanFactor_of_scaled_localDensity_countOne
    {delta a b : NNReal} {plankCount tubesPerPlank totalCount : Nat}
    {average d outerBound geometricScale sourceFactor rawLoss geometryLoss
      targetCF densityLoss countLoss : ENNReal}
    {epsilon beta : Real}
    (hdelta : 0 < delta) (ha : 0 < a) (hb : 0 < b)
    (hbeta0 : 0 <= beta) (hbetaOne : beta <= 1)
    (hsource0 : sourceFactor ≠ 0) (hsourceTop : sourceFactor ≠ ∞)
    (hd0 : d ≠ 0) (hdTop : d ≠ ∞)
    (hdcard : d <= (tubesPerPlank : ENNReal))
    (hcount : ((plankCount * tubesPerPlank : Nat) : ENNReal) <=
      countLoss * (totalCount : ENNReal))
    (hscaled : sourceFactor * average <=
      rawLoss * (outerBound * (d * geometricScale)))
    (hgeometry : geometricScale <=
      sourceFactor * geometryLoss *
        proposition66AInnerFactor delta a b 1 epsilon beta)
    (houterJoint :
      d ^ (beta / 2) * outerBound <=
        densityLoss *
          proposition66AOuterFactor
            delta a b plankCount targetCF epsilon beta) :
    average <=
      (rawLoss * geometryLoss * densityLoss *
          countLoss ^ (1 - beta / 2)) *
        proposition66AFrostmanFactor
          delta a b totalCount targetCF epsilon beta := by
  apply average_le_wholeProp66AFrostmanFactor_of_scaled_localDensity
    hdelta ha hb hbeta0 hbetaOne hsource0 hsourceTop hd0 hdTop hcount
    hscaled houterJoint
  exact localDensityInnerJoint_of_countOne
    hbetaOne hdcard hgeometry

#print axioms proposition66AOuterFactor_eq_CF_rpow_mul_independent
#print axioms localDensityResidual_mul_outerFactor_le
#print axioms proposition66AInnerFactor_eq_countOne_mul_card_rpow
#print axioms outerBound_mul_localDensityGeometricScale_le_jointProp66AProduct
#print axioms localDensityInnerJoint_of_countOne
#print axioms outerBound_mul_localDensityGeometricScale_le_jointProp66AProduct_of_countOne
#print axioms average_le_wholeProp66AFrostmanFactor_of_scaled_localDensity
#print axioms average_le_wholeProp66AFrostmanFactor_of_scaled_localDensity_countOne

end
end Family8ComparableRLocalKTWholeEq32ScalarV1
