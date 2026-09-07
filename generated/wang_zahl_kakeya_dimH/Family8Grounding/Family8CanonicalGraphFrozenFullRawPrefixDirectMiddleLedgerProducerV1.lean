import Family8Grounding.Family8CanonicalGraphFrozenActualLedgerOuterFactorJointPaymentV1
import Family8Grounding.Family8CanonicalGraphFrozenCoreNativeResidualFirstScaleLedgerBridgeV1
import Mathlib.Tactic

/-!
# Direct-middle producer for the full raw reverse-ledger prefix

The full-raw terminal asks for

`collapsedPrefix * A.frozenCoarse.averageMultiplicity
    <= cumulativeReverseLoss * F(delta, rho, middleCount)`.

This file shows that this is exactly the natural output of the direct-middle
estimate once the first scale pays the residual reverse loss.  The proof uses
the literal frozen average only once: it cancels the denominator in
`residualFirstLedgerLoss`.  In particular, no H-row factor is introduced.

The second half exposes an honest cardinality-normalized sufficient condition
for the remaining first-scale payment.  It does not assert that condition
without a geometric producer.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

open scoped BigOperators ENNReal NNReal

namespace Family8CanonicalGraphFrozenFullRawPrefixDirectMiddleLedgerProducerV1

open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8CanonicalGraphFrozenActualLedgerOuterFactorJointPaymentV1
open Family8CanonicalGraphFrozenCoreNativeResidualFirstScaleLedgerBridgeV1
open Family8CanonicalGraphFrozenRawEq66IdentityBridgeV1
open Family8CorrelatedEq66ActualFrozenThirdLedgerBindingV1
open Family8ParentwiseBadParentActualFactorListSuccessorV1
open Family8ParentwiseBadParentRepeatedSuccessorLedgerV1
open Family8RepeatedBadParentLedgerCorrelatedEq66ConnectorV1
open Family8ThreeScaleFrostmanFactorAlgebraV2
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

/-! ## Scalar full-raw composition -/

/-- The weakest joint scalar payment needed after the direct-middle estimate.
Unlike `fullRawPrefix_of_directMiddle_and_residualFirst` below, this statement
keeps the useful factor `delta^(10*eta)` attached to the actual frozen
average.  Thus neither that gain nor any part of the reverse ledger is
discarded, and no H-row factor is introduced. -/
theorem fullRawPrefix_of_directMiddle_and_gainWeightedPayment
    {delta tau rho : NNReal} {eta gamma : Real} {middleCount : Nat}
    {rawPrefix actualAverage reverseLoss : ENNReal}
    (hdelta : 0 < delta) (htau : 0 < tau) (hrho : 0 < rho)
    (hgammaTwo : gamma <= 2)
    (hDirect : rawPrefix <=
      (delta : ENNReal) ^ (10 * eta) *
        sectionEightScaleCountFrostmanFactor
          tau rho middleCount gamma)
    (hPayment :
      (delta : ENNReal) ^ (10 * eta) * actualAverage <=
        reverseLoss *
          sectionEightScaleCountFrostmanFactor delta tau 1 gamma) :
    rawPrefix * actualAverage <=
      reverseLoss *
        sectionEightScaleCountFrostmanFactor
          delta rho middleCount gamma := by
  have hFactor :
      sectionEightScaleCountFrostmanFactor delta tau 1 gamma *
          sectionEightScaleCountFrostmanFactor tau rho middleCount gamma =
        sectionEightScaleCountFrostmanFactor delta rho middleCount gamma := by
    simpa only [one_mul] using
      (sectionEightScaleCountFrostmanFactor_mul
        hdelta htau hrho hgammaTwo
          (firstCount := 1) (secondCount := middleCount))
  calc
    rawPrefix * actualAverage <=
        ((delta : ENNReal) ^ (10 * eta) *
          sectionEightScaleCountFrostmanFactor tau rho middleCount gamma) *
            actualAverage := mul_le_mul' hDirect le_rfl
    _ = ((delta : ENNReal) ^ (10 * eta) * actualAverage) *
          sectionEightScaleCountFrostmanFactor
            tau rho middleCount gamma := by ac_rfl
    _ <= (reverseLoss *
          sectionEightScaleCountFrostmanFactor delta tau 1 gamma) *
        sectionEightScaleCountFrostmanFactor
          tau rho middleCount gamma := mul_le_mul' hPayment le_rfl
    _ = reverseLoss *
        (sectionEightScaleCountFrostmanFactor delta tau 1 gamma *
          sectionEightScaleCountFrostmanFactor
            tau rho middleCount gamma) := by ac_rfl
    _ = reverseLoss *
        sectionEightScaleCountFrostmanFactor
          delta rho middleCount gamma := by
      rw [hFactor]

/-- A run-free local first-scale estimate supplies the weakest joint payment
as soon as the reverse loss is at least one.  For the endpoint identity
sequence the first-scale factor is definitionally one, so the remaining
analytic assertion is exactly
`delta^(10*eta) * actualAverage <= 1`. -/
theorem fullRawPrefix_of_directMiddle_and_localFirstScalePayment
    {delta tau rho : NNReal} {eta gamma : Real} {middleCount : Nat}
    {rawPrefix actualAverage reverseLoss : ENNReal}
    (hdelta : 0 < delta) (htau : 0 < tau) (hrho : 0 < rho)
    (hgammaTwo : gamma <= 2)
    (hDirect : rawPrefix <=
      (delta : ENNReal) ^ (10 * eta) *
        sectionEightScaleCountFrostmanFactor
          tau rho middleCount gamma)
    (hReverseOne : 1 <= reverseLoss)
    (hLocal :
      (delta : ENNReal) ^ (10 * eta) * actualAverage <=
        sectionEightScaleCountFrostmanFactor delta tau 1 gamma) :
    rawPrefix * actualAverage <=
      reverseLoss *
        sectionEightScaleCountFrostmanFactor
          delta rho middleCount gamma := by
  apply fullRawPrefix_of_directMiddle_and_gainWeightedPayment
    hdelta htau hrho hgammaTwo hDirect
  calc
    (delta : ENNReal) ^ (10 * eta) * actualAverage <=
        sectionEightScaleCountFrostmanFactor delta tau 1 gamma := hLocal
    _ = 1 * sectionEightScaleCountFrostmanFactor delta tau 1 gamma := by
      rw [one_mul]
    _ <= reverseLoss *
        sectionEightScaleCountFrostmanFactor delta tau 1 gamma :=
      mul_le_mul' hReverseOne le_rfl

/-- Endpoint form of the weakest payment.  Here the direct middle already
starts at `delta`, so there is no first-scale factor at all: the exact scalar
seam is `delta^(10*eta) * actualAverage <= reverseLoss`. -/
theorem fullRawPrefix_of_endpointDirectMiddle_and_gainWeightedPayment
    {delta rho : NNReal} {eta gamma : Real} {middleCount : Nat}
    {rawPrefix actualAverage reverseLoss : ENNReal}
    (hDirect : rawPrefix <=
      (delta : ENNReal) ^ (10 * eta) *
        sectionEightScaleCountFrostmanFactor
          delta rho middleCount gamma)
    (hPayment :
      (delta : ENNReal) ^ (10 * eta) * actualAverage <= reverseLoss) :
    rawPrefix * actualAverage <=
      reverseLoss *
        sectionEightScaleCountFrostmanFactor
          delta rho middleCount gamma := by
  calc
    rawPrefix * actualAverage <=
        ((delta : ENNReal) ^ (10 * eta) *
          sectionEightScaleCountFrostmanFactor delta rho middleCount gamma) *
            actualAverage := mul_le_mul' hDirect le_rfl
    _ = ((delta : ENNReal) ^ (10 * eta) * actualAverage) *
          sectionEightScaleCountFrostmanFactor
            delta rho middleCount gamma := by ac_rfl
    _ <= reverseLoss *
        sectionEightScaleCountFrostmanFactor
          delta rho middleCount gamma := mul_le_mul' hPayment le_rfl

/-- Useful endpoint sufficient form when the reverse ledger is known to be
at least one, as it is for a selector-grounded paper-factor run. -/
theorem fullRawPrefix_of_endpointDirectMiddle_and_averageGain
    {delta rho : NNReal} {eta gamma : Real} {middleCount : Nat}
    {rawPrefix actualAverage reverseLoss : ENNReal}
    (hDirect : rawPrefix <=
      (delta : ENNReal) ^ (10 * eta) *
        sectionEightScaleCountFrostmanFactor
          delta rho middleCount gamma)
    (hAverageGain :
      (delta : ENNReal) ^ (10 * eta) * actualAverage <= 1)
    (hReverseOne : 1 <= reverseLoss) :
    rawPrefix * actualAverage <=
      reverseLoss *
        sectionEightScaleCountFrostmanFactor
          delta rho middleCount gamma := by
  exact fullRawPrefix_of_endpointDirectMiddle_and_gainWeightedPayment
    hDirect (hAverageGain.trans hReverseOne)

/-- A direct middle estimate and the literal residual-first payment produce
the full raw prefix.  The gain `delta^(10*eta)` is harmless because it is at
most one. -/
theorem fullRawPrefix_of_directMiddle_and_residualFirst
    {delta tau rho : NNReal} {eta gamma : Real} {middleCount : Nat}
    {rawPrefix : ENNReal}
    {fineIndex coarseIndex : Type}
    [Fintype fineIndex] [DecidableEq fineIndex]
    [Fintype coarseIndex] [DecidableEq coarseIndex]
    {fine : UniformTubeFamily tau fineIndex}
    {G : ConvexFamily coarseIndex}
    {Y : Shading fine.bodyFamily}
    {Q : ConvexFactorization fine.bodyFamily G}
    (A : Family8FrozenNeighborhoodAssemblyV1.Assembly Q Y 1)
    {sourceFactors finalFactors : List ActualFactorDatum}
    (ledger : RepeatedBadParentLedger sourceFactors finalFactors)
    (hdelta : 0 < delta) (hdeltaOne : delta <= 1)
    (htau : 0 < tau) (hrho : 0 < rho)
    (heta : 0 <= eta) (hgammaTwo : gamma <= 2)
    (hDirect : rawPrefix <=
      (delta : ENNReal) ^ (10 * eta) *
        sectionEightScaleCountFrostmanFactor
          tau rho middleCount gamma)
    (hFirstScale : 1 <=
      residualFirstLedgerLoss ledger A *
        sectionEightScaleCountFrostmanFactor delta tau 1 gamma) :
    rawPrefix * A.frozenCoarse.averageMultiplicity <=
      cumulativeReverseLoss ledger *
        sectionEightScaleCountFrostmanFactor
          delta rho middleCount gamma := by
  have hFactor :
      sectionEightScaleCountFrostmanFactor delta tau 1 gamma *
          sectionEightScaleCountFrostmanFactor tau rho middleCount gamma =
        sectionEightScaleCountFrostmanFactor delta rho middleCount gamma := by
    simpa only [one_mul] using
      (sectionEightScaleCountFrostmanFactor_mul
        hdelta htau hrho hgammaTwo
          (firstCount := 1) (secondCount := middleCount))
  have hMiddle :
      sectionEightScaleCountFrostmanFactor tau rho middleCount gamma <=
        residualFirstLedgerLoss ledger A *
          sectionEightScaleCountFrostmanFactor delta rho middleCount gamma := by
    calc
      sectionEightScaleCountFrostmanFactor tau rho middleCount gamma =
          1 * sectionEightScaleCountFrostmanFactor
            tau rho middleCount gamma := by rw [one_mul]
      _ <= (residualFirstLedgerLoss ledger A *
              sectionEightScaleCountFrostmanFactor delta tau 1 gamma) *
            sectionEightScaleCountFrostmanFactor
              tau rho middleCount gamma :=
        mul_le_mul' hFirstScale le_rfl
      _ = residualFirstLedgerLoss ledger A *
          (sectionEightScaleCountFrostmanFactor delta tau 1 gamma *
            sectionEightScaleCountFrostmanFactor
              tau rho middleCount gamma) := by ac_rfl
      _ = residualFirstLedgerLoss ledger A *
          sectionEightScaleCountFrostmanFactor
            delta rho middleCount gamma := by rw [hFactor]
  have hGained : rawPrefix <=
      (delta : ENNReal) ^ (10 * eta) *
        (residualFirstLedgerLoss ledger A *
          sectionEightScaleCountFrostmanFactor
            delta rho middleCount gamma) :=
    hDirect.trans (mul_le_mul' le_rfl hMiddle)
  have hdeltaENN : (delta : ENNReal) <= 1 := by
    exact_mod_cast hdeltaOne
  have hgainNonneg : 0 <= 10 * eta := by positivity
  have hgainOne : (delta : ENNReal) ^ (10 * eta) <= 1 :=
    ENNReal.rpow_le_one hdeltaENN hgainNonneg
  have hsplit := residualFirst_mul_actualFrozenThird_le_reverse ledger A
  calc
    rawPrefix * A.frozenCoarse.averageMultiplicity <=
        ((delta : ENNReal) ^ (10 * eta) *
          (residualFirstLedgerLoss ledger A *
            sectionEightScaleCountFrostmanFactor
              delta rho middleCount gamma)) *
          A.frozenCoarse.averageMultiplicity :=
      mul_le_mul' hGained le_rfl
    _ = (delta : ENNReal) ^ (10 * eta) *
        ((residualFirstLedgerLoss ledger A *
            actualFrozenThirdLedgerLoss A) *
          sectionEightScaleCountFrostmanFactor
            delta rho middleCount gamma) := by
      unfold actualFrozenThirdLedgerLoss
      ac_rfl
    _ <= 1 *
        (cumulativeReverseLoss ledger *
          sectionEightScaleCountFrostmanFactor
            delta rho middleCount gamma) :=
      mul_le_mul' hgainOne (mul_le_mul' hsplit le_rfl)
    _ = cumulativeReverseLoss ledger *
        sectionEightScaleCountFrostmanFactor
          delta rho middleCount gamma := by rw [one_mul]

/-! ## Cardinality-normalized first-scale producer -/

/-- On a same-assembly graph identity, the first-scale residual premise
follows from the exact count-normalized payment of the actual frozen average.
The nonzero/finite facts needed for division are automatic for this literal
assembly. -/
theorem sameAssembly_residualFirst_mul_factor_ge_one_of_countBudget
    {tau rho : NNReal} {fineIndex : Type}
    [Fintype fineIndex] [DecidableEq fineIndex]
    {F : UniformTubeFamily tau fineIndex}
    {T : StickyScaleCover F rho}
    {P : ConvexFactorization F.bodyFamily T.coarse.bodyFamily}
    {Y : Shading F.bodyFamily} {fibreCF : ENNReal}
    (R : SameAssemblyFullCoefficientGraphIdentity F T P Y fibreCF)
    {sourceFactors finalFactors : List ActualFactorDatum}
    (ledger : RepeatedBadParentLedger sourceFactors finalFactors)
    (firstScaleFactor : ENNReal)
    (hfinal0 : factorCardProduct finalFactors ≠ 0)
    (hfinalTop : factorCardProduct finalFactors ≠ ∞)
    (hcountBudget :
      actualFrozenThirdLedgerLoss R.A * factorCardProduct finalFactors <=
        factorCardProduct sourceFactors * firstScaleFactor) :
    1 <= residualFirstLedgerLoss ledger R.A * firstScaleFactor := by
  have hthird := thirdLoss_le_reverse_mul_factor_of_countBudget
    ledger hfinal0 hfinalTop hcountBudget
  change 1 <=
    (cumulativeReverseLoss ledger /
      actualFrozenThirdLedgerLoss R.A) * firstScaleFactor
  exact (one_le_div_mul_iff
    (sameAssembly_actualFrozenThirdLedgerLoss_ne_zero R)
    (sameAssembly_actualFrozenThirdLedgerLoss_ne_top R)).2 hthird

/-- Combined direct-middle/cardinality producer for the exact `hFullRawPrefix`
shape consumed by the full-reverse terminal. -/
theorem sameAssembly_fullRawPrefix_of_directMiddle_and_countBudget
    {delta tau rho : NNReal} {eta gamma : Real} {middleCount : Nat}
    {fineIndex : Type}
    [Fintype fineIndex] [DecidableEq fineIndex]
    {F : UniformTubeFamily tau fineIndex}
    {T : StickyScaleCover F rho}
    {P : ConvexFactorization F.bodyFamily T.coarse.bodyFamily}
    {Y : Shading F.bodyFamily} {fibreCF : ENNReal}
    (R : SameAssemblyFullCoefficientGraphIdentity F T P Y fibreCF)
    {sourceFactors finalFactors : List ActualFactorDatum}
    (ledger : RepeatedBadParentLedger sourceFactors finalFactors)
    (firstCap : ENNReal) (lossEta : Real)
    (hdelta : 0 < delta) (hdeltaOne : delta <= 1)
    (htau : 0 < tau) (hrho : 0 < rho)
    (heta : 0 <= eta) (hgammaTwo : gamma <= 2)
    (hDirect : R.collapsedPrefix (delta := delta) firstCap lossEta <=
      (delta : ENNReal) ^ (10 * eta) *
        sectionEightScaleCountFrostmanFactor
          tau rho middleCount gamma)
    (hfinal0 : factorCardProduct finalFactors ≠ 0)
    (hfinalTop : factorCardProduct finalFactors ≠ ∞)
    (hcountBudget :
      actualFrozenThirdLedgerLoss R.A * factorCardProduct finalFactors <=
        factorCardProduct sourceFactors *
          sectionEightScaleCountFrostmanFactor delta tau 1 gamma) :
    R.collapsedPrefix (delta := delta) firstCap lossEta *
        R.A.frozenCoarse.averageMultiplicity <=
      cumulativeReverseLoss ledger *
        sectionEightScaleCountFrostmanFactor
          delta rho middleCount gamma := by
  apply fullRawPrefix_of_directMiddle_and_residualFirst
    R.A ledger hdelta hdeltaOne htau hrho heta hgammaTwo hDirect
  exact sameAssembly_residualFirst_mul_factor_ge_one_of_countBudget
    R ledger
      (sectionEightScaleCountFrostmanFactor delta tau 1 gamma)
      hfinal0 hfinalTop hcountBudget

#print axioms fullRawPrefix_of_directMiddle_and_gainWeightedPayment
#print axioms fullRawPrefix_of_directMiddle_and_localFirstScalePayment
#print axioms fullRawPrefix_of_endpointDirectMiddle_and_gainWeightedPayment
#print axioms fullRawPrefix_of_endpointDirectMiddle_and_averageGain
#print axioms fullRawPrefix_of_directMiddle_and_residualFirst
#print axioms sameAssembly_residualFirst_mul_factor_ge_one_of_countBudget
#print axioms sameAssembly_fullRawPrefix_of_directMiddle_and_countBudget

end
end Family8CanonicalGraphFrozenFullRawPrefixDirectMiddleLedgerProducerV1
