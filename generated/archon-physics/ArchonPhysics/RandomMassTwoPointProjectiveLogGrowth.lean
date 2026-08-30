import ArchonPhysics.RandomMassTwoPointProjectiveStationary
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Stationary logarithmic growth for the two-point transfer law

This file constructs the integrable cocycle entering Furstenberg's formula
for the concrete equal-weight two-mass transfer process.  On the unit-sphere
double cover of the real projective line the one-step increment is

`log ‖T(m, lambda) v‖`.

It is continuous (the determinant-one transfer never annihilates a unit
direction), hence bounded and integrable against every projective probability
law.  We bundle the equal-weight one-step expectation and its stationary
integral formula, and package it with the previously proved noncompactness,
projective strong irreducibility, and existence of a stationary law.

The package is exactly an input interface for a classical Furstenberg
positivity theorem.  Such a theorem is not present in the current library, so
this file does **not** assert positivity of the stationary integral, a positive
Lyapunov exponent, EFC, or localization.
-/

open scoped NNReal Topology BoundedContinuousFunction

namespace ArchonPhysics.RandomMassTwoPointProjectiveLogGrowth

open ArchonPhysics.RandomMassTwoPointProjectiveMarkov
open ArchonPhysics.RandomMassTwoPointProjectiveStationary
open ArchonPhysics.RandomMassTwoStepAnnealedTransferGrowth
open MeasureTheory

noncomputable section

/-- The logarithmic norm increment of one transfer step from a unit
direction.  Since the input direction has norm one, no denominator is needed. -/
def transferLogNormCocycle
    (lambda mass : Real) (direction : OrientedProjectiveDirection) : Real :=
  Real.log ‖oneStepTransferState lambda mass
    (direction : TransferVector)‖

/-- The one-step logarithmic norm cocycle is continuous on the compact
oriented projective direction space. -/
theorem continuous_transferLogNormCocycle (lambda mass : Real) :
    Continuous (transferLogNormCocycle lambda mass) := by
  have hstep : Continuous (fun direction : OrientedProjectiveDirection =>
      oneStepTransferState lambda mass (direction : TransferVector)) :=
    (continuous_oneStepTransferState lambda mass).comp continuous_subtype_val
  exact hstep.norm.log (fun direction =>
    norm_ne_zero_iff.mpr
      (oneStepTransferState_direction_ne_zero lambda mass direction))

/-- The logarithmic norm increment as a bounded continuous observable. -/
def transferLogNormObservable (lambda mass : Real) :
    OrientedProjectiveDirection →ᵇ Real :=
  ContinuousMap.equivBoundedOfCompact
    OrientedProjectiveDirection Real
      ⟨transferLogNormCocycle lambda mass,
        continuous_transferLogNormCocycle lambda mass⟩

@[simp]
theorem transferLogNormObservable_apply
    (lambda mass : Real) (direction : OrientedProjectiveDirection) :
    transferLogNormObservable lambda mass direction =
      transferLogNormCocycle lambda mass direction :=
  rfl

/-- Compact projective directions make the one-step logarithmic norm
increment integrable against every probability law.  For the two-atom mass
law this supplies the finite logarithmic moment separately at both atoms. -/
theorem integrable_transferLogNormCocycle
    (lambda mass : Real)
    (law : ProbabilityMeasure OrientedProjectiveDirection) :
    Integrable (transferLogNormCocycle lambda mass)
      (law : Measure OrientedProjectiveDirection) := by
  change Integrable (fun direction =>
    transferLogNormObservable lambda mass direction)
      (law : Measure OrientedProjectiveDirection)
  exact (transferLogNormObservable lambda mass).integrable
    (law : Measure OrientedProjectiveDirection)

/-- The conditional one-step logarithmic increment for the equal-weight
two-atom mass law. -/
def twoPointLogGrowthObservable
    (lambda mass0 mass1 : Real) :
    OrientedProjectiveDirection →ᵇ Real :=
  ContinuousMap.equivBoundedOfCompact
    OrientedProjectiveDirection Real
      ⟨fun direction =>
          (transferLogNormCocycle lambda mass0 direction +
            transferLogNormCocycle lambda mass1 direction) / 2,
        ((continuous_transferLogNormCocycle lambda mass0).add
          (continuous_transferLogNormCocycle lambda mass1)).div_const 2⟩

@[simp]
theorem twoPointLogGrowthObservable_apply
    (lambda mass0 mass1 : Real)
    (direction : OrientedProjectiveDirection) :
    twoPointLogGrowthObservable lambda mass0 mass1 direction =
      (transferLogNormCocycle lambda mass0 direction +
        transferLogNormCocycle lambda mass1 direction) / 2 :=
  rfl

/-- The equal-weight one-step increment is integrable for every direction
law. -/
theorem integrable_twoPointLogGrowthObservable
    (lambda mass0 mass1 : Real)
    (law : ProbabilityMeasure OrientedProjectiveDirection) :
    Integrable (fun direction =>
      twoPointLogGrowthObservable lambda mass0 mass1 direction)
      (law : Measure OrientedProjectiveDirection) :=
  (twoPointLogGrowthObservable lambda mass0 mass1).integrable
    (law : Measure OrientedProjectiveDirection)

/-- Furstenberg's stationary one-step average, defined without asserting its
sign.  The name records the intended use; stationarity is imposed in the
theorems and certificate below. -/
def twoPointStationaryLogGrowthRate
    (lambda mass0 mass1 : Real)
    (law : ProbabilityMeasure OrientedProjectiveDirection) : Real :=
  ∫ direction, twoPointLogGrowthObservable lambda mass0 mass1 direction
    ∂(law : Measure OrientedProjectiveDirection)

/-- The stationary growth functional is exactly the equal-weight one-step
expectation over the two mass atoms and the projective law. -/
theorem twoPointStationaryLogGrowthRate_eq_oneStepExpectation
    (lambda mass0 mass1 : Real)
    (law : ProbabilityMeasure OrientedProjectiveDirection) :
    twoPointStationaryLogGrowthRate lambda mass0 mass1 law =
      ((∫ direction, transferLogNormCocycle lambda mass0 direction
          ∂(law : Measure OrientedProjectiveDirection)) +
        ∫ direction, transferLogNormCocycle lambda mass1 direction
          ∂(law : Measure OrientedProjectiveDirection)) / 2 := by
  rw [twoPointStationaryLogGrowthRate]
  simp only [twoPointLogGrowthObservable_apply]
  rw [integral_div, integral_add
    (integrable_transferLogNormCocycle lambda mass0 law)
    (integrable_transferLogNormCocycle lambda mass1 law)]

/-- Stationarity is equivalently the invariance of the integral of every
bounded continuous projective observable under one equal-weight transfer
step. -/
theorem integral_eq_twoPoint_next_of_stationary
    {lambda mass0 mass1 : Real}
    {law : ProbabilityMeasure OrientedProjectiveDirection}
    (hstationary :
      IsTwoPointProjectiveStationary lambda mass0 mass1 law)
    (observable : OrientedProjectiveDirection →ᵇ Real) :
    (∫ direction, observable direction
      ∂(law : Measure OrientedProjectiveDirection)) =
      ((∫ direction, observable
          (normalizedTransferDirection lambda mass0 direction)
          ∂(law : Measure OrientedProjectiveDirection)) +
        ∫ direction, observable
          (normalizedTransferDirection lambda mass1 direction)
          ∂(law : Measure OrientedProjectiveDirection)) / 2 := by
  have hduality := integral_twoPointProjectiveMarkovOperator
    lambda mass0 mass1 law observable
  rw [hstationary] at hduality
  exact hduality

/-- The exact no-axiom input package available for the classical
two-dimensional Furstenberg positivity theorem.  Its fields contain
noncompactness, projective strong irreducibility, an actual stationary law,
and the finite logarithmic moment/stationary integral interface. -/
structure TwoPointFurstenbergIntegralCertificate
    (lambda mass0 mass1 : Real)
    (law : ProbabilityMeasure OrientedProjectiveDirection) : Prop where
  prerequisites :
    TwoPointProjectivePrerequisiteCertificate lambda mass0 mass1
  stationary :
    IsTwoPointProjectiveStationary lambda mass0 mass1 law
  mass0LogIncrementIntegrable :
    Integrable (transferLogNormCocycle lambda mass0)
      (law : Measure OrientedProjectiveDirection)
  mass1LogIncrementIntegrable :
    Integrable (transferLogNormCocycle lambda mass1)
      (law : Measure OrientedProjectiveDirection)
  oneStepLogIncrementIntegrable :
    Integrable (fun direction =>
      twoPointLogGrowthObservable lambda mass0 mass1 direction)
      (law : Measure OrientedProjectiveDirection)
  stationaryIntegralFormula :
    twoPointStationaryLogGrowthRate lambda mass0 mass1 law =
      ((∫ direction, transferLogNormCocycle lambda mass0 direction
          ∂(law : Measure OrientedProjectiveDirection)) +
        ∫ direction, transferLogNormCocycle lambda mass1 direction
          ∂(law : Measure OrientedProjectiveDirection)) / 2
  stationaryObservableIdentity :
    ∀ observable : OrientedProjectiveDirection →ᵇ Real,
      (∫ direction, observable direction
        ∂(law : Measure OrientedProjectiveDirection)) =
        ((∫ direction, observable
            (normalizedTransferDirection lambda mass0 direction)
            ∂(law : Measure OrientedProjectiveDirection)) +
          ∫ direction, observable
            (normalizedTransferDirection lambda mass1 direction)
            ∂(law : Measure OrientedProjectiveDirection)) / 2

/-- Positive parameter, distinct atoms, and a stationary law construct the
complete integral certificate without any positivity theorem. -/
theorem twoPointFurstenbergIntegralCertificate_of_stationary
    {lambda mass0 mass1 : Real}
    {law : ProbabilityMeasure OrientedProjectiveDirection}
    (hlambda : 0 < lambda) (hmass : mass0 ≠ mass1)
    (hstationary :
      IsTwoPointProjectiveStationary lambda mass0 mass1 law) :
    TwoPointFurstenbergIntegralCertificate
      lambda mass0 mass1 law where
  prerequisites :=
    twoPointProjectivePrerequisiteCertificate_of_distinct hlambda hmass
  stationary := hstationary
  mass0LogIncrementIntegrable :=
    integrable_transferLogNormCocycle lambda mass0 law
  mass1LogIncrementIntegrable :=
    integrable_transferLogNormCocycle lambda mass1 law
  oneStepLogIncrementIntegrable :=
    integrable_twoPointLogGrowthObservable lambda mass0 mass1 law
  stationaryIntegralFormula :=
    twoPointStationaryLogGrowthRate_eq_oneStepExpectation
      lambda mass0 mass1 law
  stationaryObservableIdentity :=
    integral_eq_twoPoint_next_of_stationary hstationary

/-- The exact missing analytic conclusion.  A suitable classical
Furstenberg positivity theorem would derive this predicate from the
certificate above; no such implication is asserted here. -/
def HasPositiveTwoPointStationaryLogGrowth
    (lambda mass0 mass1 : Real)
    (law : ProbabilityMeasure OrientedProjectiveDirection) : Prop :=
  0 < twoPointStationaryLogGrowthRate lambda mass0 mass1 law

end

end ArchonPhysics.RandomMassTwoPointProjectiveLogGrowth
