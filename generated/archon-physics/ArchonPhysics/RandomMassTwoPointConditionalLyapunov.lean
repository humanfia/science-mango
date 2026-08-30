import ArchonPhysics.RandomMassTwoPointProjectiveLogGrowth
import Mathlib.Analysis.Complex.Exponential

/-!
# Conditional two-point Lyapunov endpoint

This file isolates the single analytic theorem still missing from the local
library: classical Furstenberg positivity for the already constructed
two-point stationary integral certificate.  The interface is an implication
from that certificate to strict positivity; positivity is not inserted as a
field of the certificate and no new axiom is declared.

Independently of positivity, we prove the genuine logarithmic cocycle identity
and construct the equal-weight binary-tree average of its first `n`
increments.  Stationarity makes its integral exactly `n` times the one-step
Furstenberg integral.  Assuming the one external positivity interface then
gives a positive conditional Lyapunov endpoint and exponential growth of the
stationary geometric mean.

This is a conditional two-atom random-transfer conclusion.  It is not EFC,
localization, a small-denominator estimate, or a theorem for the full
continuous uniform mass law.
-/

open scoped NNReal Topology BoundedContinuousFunction

namespace ArchonPhysics.RandomMassTwoPointConditionalLyapunov

open ArchonPhysics.RandomMassTwoPointProjectiveLogGrowth
open ArchonPhysics.RandomMassTwoPointProjectiveMarkov
open ArchonPhysics.RandomMassTwoPointProjectiveStationary
open ArchonPhysics.RandomMassTwoStepAnnealedTransferGrowth
open MeasureTheory

noncomputable section

/-! ## The genuine additive logarithmic cocycle -/

/-- A fixed transfer step is real-linear in the state vector. -/
theorem oneStepTransferState_smul
    (lambda mass scalar : Real) (state : TransferVector) :
    oneStepTransferState lambda mass (scalar • state) =
      scalar • oneStepTransferState lambda mass state := by
  unfold oneStepTransferState
  exact Matrix.mulVec_smul _ _ _

/-- Normalizing after the first step loses exactly the positive norm factor,
which can be reconstructed before applying the second step. -/
theorem norm_smul_oneStep_normalizedTransferDirection
    (lambda mass0 mass1 : Real)
    (direction : OrientedProjectiveDirection) :
    ‖oneStepTransferState lambda mass0 (direction : TransferVector)‖ •
        oneStepTransferState lambda mass1
          (normalizedTransferDirection lambda mass0 direction :
            TransferVector) =
      oneStepTransferState lambda mass1
        (oneStepTransferState lambda mass0
          (direction : TransferVector)) := by
  rw [← oneStepTransferState_smul]
  change oneStepTransferState lambda mass1
      (‖oneStepTransferState lambda mass0
          (direction : TransferVector)‖ •
        NormedSpace.normalize
          (oneStepTransferState lambda mass0
            (direction : TransferVector))) = _
  rw [NormedSpace.norm_smul_normalize]

/-- The logarithmic increment is a genuine additive cocycle under two
successive normalized projective steps. -/
theorem transferLogNormCocycle_add
    (lambda mass0 mass1 : Real)
    (direction : OrientedProjectiveDirection) :
    transferLogNormCocycle lambda mass1
        (normalizedTransferDirection lambda mass0 direction) +
      transferLogNormCocycle lambda mass0 direction =
    Real.log ‖oneStepTransferState lambda mass1
      (oneStepTransferState lambda mass0
        (direction : TransferVector))‖ := by
  have hfirst : oneStepTransferState lambda mass0
      (direction : TransferVector) ≠ 0 :=
    oneStepTransferState_direction_ne_zero lambda mass0 direction
  have hfirstNorm : ‖oneStepTransferState lambda mass0
      (direction : TransferVector)‖ ≠ 0 :=
    norm_ne_zero_iff.mpr hfirst
  have hsecond : oneStepTransferState lambda mass1
      (normalizedTransferDirection lambda mass0 direction :
        TransferVector) ≠ 0 :=
    oneStepTransferState_direction_ne_zero lambda mass1
      (normalizedTransferDirection lambda mass0 direction)
  have hsecondNorm : ‖oneStepTransferState lambda mass1
      (normalizedTransferDirection lambda mass0 direction :
        TransferVector)‖ ≠ 0 :=
    norm_ne_zero_iff.mpr hsecond
  have hreconstruct := congrArg norm
    (norm_smul_oneStep_normalizedTransferDirection
      lambda mass0 mass1 direction)
  have hnormProduct :
      ‖oneStepTransferState lambda mass0
          (direction : TransferVector)‖ *
        ‖oneStepTransferState lambda mass1
          (normalizedTransferDirection lambda mass0 direction :
            TransferVector)‖ =
      ‖oneStepTransferState lambda mass1
        (oneStepTransferState lambda mass0
          (direction : TransferVector))‖ := by
    simpa only [norm_smul, Real.norm_of_nonneg (norm_nonneg _)] using
      hreconstruct
  unfold transferLogNormCocycle
  rw [← Real.log_mul hsecondNorm hfirstNorm]
  rw [mul_comm, hnormProduct]

/-! ## Equal-weight path-averaged `n`-step logarithmic growth -/

/-- The binary-tree expectation of the accumulated logarithmic cocycle over
the first `n` independent equal-weight mass choices.  The recursion is the
literal one-step increment plus the average of both possible continuation
trees. -/
def twoPointAccumulatedLogGrowthObservable
    (lambda mass0 mass1 : Real) :
    Nat → OrientedProjectiveDirection →ᵇ Real
  | 0 => 0
  | n + 1 =>
      twoPointLogGrowthObservable lambda mass0 mass1 +
        (2 : Real)⁻¹ •
          (observableAfterNormalizedTransfer lambda mass0
              (twoPointAccumulatedLogGrowthObservable
                lambda mass0 mass1 n) +
            observableAfterNormalizedTransfer lambda mass1
              (twoPointAccumulatedLogGrowthObservable
                lambda mass0 mass1 n))

@[simp]
theorem twoPointAccumulatedLogGrowthObservable_zero
    (lambda mass0 mass1 : Real) :
    twoPointAccumulatedLogGrowthObservable lambda mass0 mass1 0 = 0 :=
  rfl

/-- Pointwise recursion exhibiting the equal-weight path expectation. -/
theorem twoPointAccumulatedLogGrowthObservable_succ_apply
    (lambda mass0 mass1 : Real) (n : Nat)
    (direction : OrientedProjectiveDirection) :
    twoPointAccumulatedLogGrowthObservable
        lambda mass0 mass1 (n + 1) direction =
      twoPointLogGrowthObservable lambda mass0 mass1 direction +
        (twoPointAccumulatedLogGrowthObservable lambda mass0 mass1 n
            (normalizedTransferDirection lambda mass0 direction) +
          twoPointAccumulatedLogGrowthObservable lambda mass0 mass1 n
            (normalizedTransferDirection lambda mass1 direction)) / 2 := by
  change
    twoPointLogGrowthObservable lambda mass0 mass1 direction +
        (2 : Real)⁻¹ *
          (twoPointAccumulatedLogGrowthObservable lambda mass0 mass1 n
              (normalizedTransferDirection lambda mass0 direction) +
            twoPointAccumulatedLogGrowthObservable lambda mass0 mass1 n
              (normalizedTransferDirection lambda mass1 direction)) = _
  ring

/-- Every finite path-averaged accumulated cocycle is integrable. -/
theorem integrable_twoPointAccumulatedLogGrowthObservable
    (lambda mass0 mass1 : Real) (n : Nat)
    (law : ProbabilityMeasure OrientedProjectiveDirection) :
    Integrable (fun direction =>
      twoPointAccumulatedLogGrowthObservable
        lambda mass0 mass1 n direction)
      (law : Measure OrientedProjectiveDirection) :=
  (twoPointAccumulatedLogGrowthObservable
    lambda mass0 mass1 n).integrable
      (law : Measure OrientedProjectiveDirection)

/-- Under a stationary direction law, adding one independent mass step adds
exactly the one-step Furstenberg integral to expected accumulated growth. -/
theorem integral_twoPointAccumulatedLogGrowthObservable_succ
    {lambda mass0 mass1 : Real}
    {law : ProbabilityMeasure OrientedProjectiveDirection}
    (hstationary :
      IsTwoPointProjectiveStationary lambda mass0 mass1 law)
    (n : Nat) :
    (∫ direction,
      twoPointAccumulatedLogGrowthObservable
        lambda mass0 mass1 (n + 1) direction
      ∂(law : Measure OrientedProjectiveDirection)) =
      twoPointStationaryLogGrowthRate lambda mass0 mass1 law +
        ∫ direction,
          twoPointAccumulatedLogGrowthObservable
            lambda mass0 mass1 n direction
          ∂(law : Measure OrientedProjectiveDirection) := by
  rw [integral_congr_ae (Filter.Eventually.of_forall
    (twoPointAccumulatedLogGrowthObservable_succ_apply
      lambda mass0 mass1 n))]
  have h0 : Integrable (fun direction =>
      twoPointAccumulatedLogGrowthObservable lambda mass0 mass1 n
        (normalizedTransferDirection lambda mass0 direction))
      (law : Measure OrientedProjectiveDirection) := by
    change Integrable (fun direction =>
      observableAfterNormalizedTransfer lambda mass0
        (twoPointAccumulatedLogGrowthObservable
          lambda mass0 mass1 n) direction)
      (law : Measure OrientedProjectiveDirection)
    exact (observableAfterNormalizedTransfer lambda mass0
      (twoPointAccumulatedLogGrowthObservable
        lambda mass0 mass1 n)).integrable
          (law : Measure OrientedProjectiveDirection)
  have h1 : Integrable (fun direction =>
      twoPointAccumulatedLogGrowthObservable lambda mass0 mass1 n
        (normalizedTransferDirection lambda mass1 direction))
      (law : Measure OrientedProjectiveDirection) := by
    change Integrable (fun direction =>
      observableAfterNormalizedTransfer lambda mass1
        (twoPointAccumulatedLogGrowthObservable
          lambda mass0 mass1 n) direction)
      (law : Measure OrientedProjectiveDirection)
    exact (observableAfterNormalizedTransfer lambda mass1
      (twoPointAccumulatedLogGrowthObservable
        lambda mass0 mass1 n)).integrable
          (law : Measure OrientedProjectiveDirection)
  have hcontinuation : Integrable (fun direction =>
      (twoPointAccumulatedLogGrowthObservable lambda mass0 mass1 n
          (normalizedTransferDirection lambda mass0 direction) +
        twoPointAccumulatedLogGrowthObservable lambda mass0 mass1 n
          (normalizedTransferDirection lambda mass1 direction)) / 2)
      (law : Measure OrientedProjectiveDirection) :=
    (h0.add h1).div_const 2
  rw [integral_add
    (integrable_twoPointLogGrowthObservable lambda mass0 mass1 law)
    hcontinuation, integral_div, integral_add h0 h1]
  rw [← integral_eq_twoPoint_next_of_stationary hstationary
    (twoPointAccumulatedLogGrowthObservable lambda mass0 mass1 n)]
  rfl

/-- The stationary expected `n`-step accumulated log norm is exactly linear
in `n`, without using positivity. -/
theorem integral_twoPointAccumulatedLogGrowthObservable_eq_nat_mul
    {lambda mass0 mass1 : Real}
    {law : ProbabilityMeasure OrientedProjectiveDirection}
    (hstationary :
      IsTwoPointProjectiveStationary lambda mass0 mass1 law)
    (n : Nat) :
    (∫ direction,
      twoPointAccumulatedLogGrowthObservable
        lambda mass0 mass1 n direction
      ∂(law : Measure OrientedProjectiveDirection)) =
      (n : Real) *
        twoPointStationaryLogGrowthRate lambda mass0 mass1 law := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [integral_twoPointAccumulatedLogGrowthObservable_succ
        hstationary n, ih]
      push_cast
      ring

/-- Dividing the stationary expected accumulated log norm by any positive
step count recovers the same one-step rate exactly. -/
theorem integral_twoPointAccumulatedLogGrowthObservable_div_natCast
    {lambda mass0 mass1 : Real}
    {law : ProbabilityMeasure OrientedProjectiveDirection}
    (hstationary :
      IsTwoPointProjectiveStationary lambda mass0 mass1 law)
    {n : Nat} (hn : n ≠ 0) :
    ((∫ direction,
      twoPointAccumulatedLogGrowthObservable
        lambda mass0 mass1 n direction
      ∂(law : Measure OrientedProjectiveDirection)) / (n : Real)) =
      twoPointStationaryLogGrowthRate lambda mass0 mass1 law := by
  rw [integral_twoPointAccumulatedLogGrowthObservable_eq_nat_mul
    hstationary n]
  exact mul_div_cancel_left₀ _ (Nat.cast_ne_zero.mpr hn)

/-- The stationary geometric mean associated with the path-averaged
`n`-step logarithmic norm. -/
def twoPointStationaryGeometricMean
    (lambda mass0 mass1 : Real)
    (law : ProbabilityMeasure OrientedProjectiveDirection)
    (n : Nat) : Real :=
  Real.exp (∫ direction,
    twoPointAccumulatedLogGrowthObservable
      lambda mass0 mass1 n direction
    ∂(law : Measure OrientedProjectiveDirection))

/-- Exponentiating stationary linear log growth gives an exact geometric
power law. -/
theorem twoPointStationaryGeometricMean_eq_pow
    {lambda mass0 mass1 : Real}
    {law : ProbabilityMeasure OrientedProjectiveDirection}
    (hstationary :
      IsTwoPointProjectiveStationary lambda mass0 mass1 law)
    (n : Nat) :
    twoPointStationaryGeometricMean lambda mass0 mass1 law n =
      (Real.exp
        (twoPointStationaryLogGrowthRate lambda mass0 mass1 law)) ^ n := by
  rw [twoPointStationaryGeometricMean,
    integral_twoPointAccumulatedLogGrowthObservable_eq_nat_mul
      hstationary n]
  exact Real.exp_nat_mul
    (twoPointStationaryLogGrowthRate lambda mass0 mass1 law) n

/-! ## The exact external theorem boundary and its conditional endpoint -/

/-- The minimal classical theorem interface missing from the current
library.  Its only mathematical input is the previously kernel-checked
certificate; it concludes strict positivity of the associated stationary
Furstenberg integral.  This definition is a proposition, not an axiom or a
field added to the certificate. -/
def ClassicalTwoPointFurstenbergPositivity : Prop :=
  ∀ {lambda mass0 mass1 : Real}
    {law : ProbabilityMeasure OrientedProjectiveDirection},
    TwoPointFurstenbergIntegralCertificate
      lambda mass0 mass1 law →
    0 < twoPointStationaryLogGrowthRate lambda mass0 mass1 law

/-- A reusable conditional Lyapunov endpoint.  It is produced only after a
caller supplies the single classical Furstenberg positivity implication. -/
structure TwoPointConditionalLyapunovEndpoint
    (lambda mass0 mass1 : Real) where
  law : ProbabilityMeasure OrientedProjectiveDirection
  certificate :
    TwoPointFurstenbergIntegralCertificate lambda mass0 mass1 law
  exponent : Real
  exponent_eq_stationaryRate :
    exponent = twoPointStationaryLogGrowthRate lambda mass0 mass1 law
  exponent_pos : 0 < exponent
  stationaryExpectedLogGrowth :
    ∀ n : Nat,
      (∫ direction,
        twoPointAccumulatedLogGrowthObservable
          lambda mass0 mass1 n direction
        ∂(law : Measure OrientedProjectiveDirection)) =
        (n : Real) * exponent
  stationaryGeometricMean :
    ∀ n : Nat,
      twoPointStationaryGeometricMean lambda mass0 mass1 law n =
        (Real.exp exponent) ^ n

/-- The external positivity interface plus a kernel-checked integral
certificate yields the conditional Lyapunov endpoint. -/
def twoPointConditionalLyapunovEndpoint_of_Furstenberg
    (hfurstenberg : ClassicalTwoPointFurstenbergPositivity)
    {lambda mass0 mass1 : Real}
    {law : ProbabilityMeasure OrientedProjectiveDirection}
    (certificate : TwoPointFurstenbergIntegralCertificate
      lambda mass0 mass1 law) :
    TwoPointConditionalLyapunovEndpoint lambda mass0 mass1 where
  law := law
  certificate := certificate
  exponent := twoPointStationaryLogGrowthRate lambda mass0 mass1 law
  exponent_eq_stationaryRate := rfl
  exponent_pos := hfurstenberg certificate
  stationaryExpectedLogGrowth :=
    integral_twoPointAccumulatedLogGrowthObservable_eq_nat_mul
      certificate.stationary
  stationaryGeometricMean :=
    twoPointStationaryGeometricMean_eq_pow certificate.stationary

/-- Every positive-time stationary geometric mean is strictly larger than
one at the conditional endpoint. -/
theorem TwoPointConditionalLyapunovEndpoint.one_lt_stationaryGeometricMean
    {lambda mass0 mass1 : Real}
    (endpoint : TwoPointConditionalLyapunovEndpoint lambda mass0 mass1)
    {n : Nat} (hn : n ≠ 0) :
    1 < twoPointStationaryGeometricMean
      lambda mass0 mass1 endpoint.law n := by
  rw [endpoint.stationaryGeometricMean n]
  exact one_lt_pow₀
    (Real.one_lt_exp_iff.mpr endpoint.exponent_pos) hn

end

end ArchonPhysics.RandomMassTwoPointConditionalLyapunov
