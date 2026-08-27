import ArchonPhysics.FiniteThreeWaveKineticGlobalFlow
import ArchonPhysics.ResonantThreeWaveMeasure

/-!
# Resonant-measure to kinetic-equation bridges

`ResonantThreeWaveMeasure` canonically supplies a weak collision functional,
but a continuum collision measure does not by itself supply a pointwise
collision density with respect to a mode reference measure.  This module
therefore keeps the two honest interfaces separate:

* on an arbitrary measurable mode space, a weak kinetic equation is stated
  relative to an explicit reference measure for the action moments;
* on a finite mode space, coordinate indicator tests canonically recover a
  genuine `CollisionData` vector field.

For an atomic measure coming from a finite collision network, the recovered
vector field is proved to be exactly the pre-existing network collision field.
No Radon--Nikodym density, continuum well-posedness, or thermodynamic kinetic
limit is asserted.
-/

namespace ArchonPhysics.ResonantThreeWaveKineticBridge

open MeasureTheory
open ArchonPhysics.FiniteThreeWaveCollisionNetwork
open ArchonPhysics.FiniteThreeWaveKineticGlobalFlow
open ArchonPhysics.ResonantThreeWaveMeasure

noncomputable section

section WeakContinuum

variable {Mode : Type*}

/-- Pair a continuum action with a test function using an explicit reference
measure on mode space.  The resonance measure alone does not determine this
reference measure. -/
def weakActionObservable [MeasurableSpace Mode]
    (reference : Measure Mode) (test action : Mode -> Real) : Real :=
  ∫ mode, test mode * action mode ∂reference

/-- A test is globally admissible for a proposed trajectory when both the
action moment and the collision integral are genuinely Bochner integrable at
every time. -/
def IsAdmissibleWeakTest [MeasurableSpace Mode]
    (collision : ResonantThreeWaveMeasure Mode) (reference : Measure Mode)
    (D : Real -> Mode -> Real) (test : Mode -> Real) : Prop :=
  forall t,
    Integrable (fun mode => test mode * D t mode) reference ∧
      Integrable (triadWeakObservableIntegrand test (D t))
        collision.collisionMeasure

/-- Weak continuum three-wave kinetic equation relative to an explicit mode
reference measure.  The right-hand side is derived from the supplied resonant
collision measure, not inserted as an arbitrary pointwise collision map.

This is a solution predicate only.  It does not assert existence, uniqueness,
positivity, or that the target random lattice supplies the reference measure
and collision measure occurring here. -/
def SolvesWeakThreeWaveKineticEquation [MeasurableSpace Mode]
    (collision : ResonantThreeWaveMeasure Mode) (reference : Measure Mode)
    (g : Real) (initial : Mode -> Real)
    (D : Real -> Mode -> Real) : Prop :=
  D 0 = initial ∧
    forall test, IsAdmissibleWeakTest collision reference D test ->
      forall t, HasDerivAt
        (fun s => weakActionObservable reference test (D s))
        (g ^ 2 * weakCollisionSlope collision test (D t)) t

/-- Additive resonance forces the weak frequency moment to have zero
derivative along every weak solution for which the frequency test is
admissible. -/
theorem weakFrequencyObservable_hasDerivAt_zero
    [MeasurableSpace Mode]
    (collision : ResonantThreeWaveMeasure Mode) (reference : Measure Mode)
    (g : Real) (initial : Mode -> Real) (D : Real -> Mode -> Real)
    (hD : SolvesWeakThreeWaveKineticEquation
      collision reference g initial D)
    (hfrequency : IsAdmissibleWeakTest
      collision reference D collision.frequency)
    (t : Real) :
    HasDerivAt
      (fun s => weakActionObservable reference collision.frequency (D s))
      0 t := by
  have hderiv := hD.2 collision.frequency hfrequency t
  rw [weakCollisionSlope_frequency_eq_zero] at hderiv
  simpa only [mul_zero] using hderiv

/-- The weak frequency moment is exactly conserved whenever its test is
globally admissible. -/
theorem weakFrequencyObservable_conserved
    [MeasurableSpace Mode]
    (collision : ResonantThreeWaveMeasure Mode) (reference : Measure Mode)
    (g : Real) (initial : Mode -> Real) (D : Real -> Mode -> Real)
    (hD : SolvesWeakThreeWaveKineticEquation
      collision reference g initial D)
    (hfrequency : IsAdmissibleWeakTest
      collision reference D collision.frequency)
    (t : Real) :
    weakActionObservable reference collision.frequency (D t) =
      weakActionObservable reference collision.frequency initial := by
  let energyMoment : Real -> Real :=
    fun s => weakActionObservable reference collision.frequency (D s)
  have hzero (s : Real) : HasDerivAt energyMoment 0 s :=
    weakFrequencyObservable_hasDerivAt_zero
      collision reference g initial D hD hfrequency s
  calc
    weakActionObservable reference collision.frequency (D t) =
        weakActionObservable reference collision.frequency (D 0) :=
      is_const_of_deriv_eq_zero
        (fun s => (hzero s).differentiableAt)
        (fun s => (hzero s).deriv) t 0
    _ = weakActionObservable reference collision.frequency initial := by
      rw [hD.1]

end WeakContinuum

section PointwiseRepresentation

variable {Mode : Type}

/-- A proof-carrying pointwise density representation of the weak collision
functional relative to a supplied mode reference measure.  Constructing this
structure is the exact additional obligation needed before a continuum
resonance measure can honestly be packaged as `CollisionData`. -/
structure PointwiseCollisionRepresentation [MeasurableSpace Mode]
    (collision : ResonantThreeWaveMeasure Mode) (reference : Measure Mode) where
  collisionVector : (Mode -> Real) -> Mode -> Real
  integrable_output : forall test action,
    Integrable (triadWeakObservableIntegrand test action)
        collision.collisionMeasure ->
      Integrable (fun mode => test mode * collisionVector action mode) reference
  represents : forall test action,
    Integrable (triadWeakObservableIntegrand test action)
        collision.collisionMeasure ->
      (∫ mode, test mode * collisionVector action mode ∂reference) =
        weakCollisionSlope collision test action

/-- Only a proof-carrying pointwise representation is converted to generic
`CollisionData`; the frequency is inherited from the same resonance measure. -/
def PointwiseCollisionRepresentation.toCollisionData
    [MeasurableSpace Mode]
    {collision : ResonantThreeWaveMeasure Mode} {reference : Measure Mode}
    (representation : PointwiseCollisionRepresentation collision reference) :
    CollisionData Mode where
  omega := collision.frequency
  collision := representation.collisionVector

@[simp] theorem PointwiseCollisionRepresentation.toCollisionData_omega
    [MeasurableSpace Mode]
    {collision : ResonantThreeWaveMeasure Mode} {reference : Measure Mode}
    (representation : PointwiseCollisionRepresentation collision reference)
    (mode : Mode) :
    representation.toCollisionData.omega mode = collision.frequency mode := by
  rfl

@[simp] theorem PointwiseCollisionRepresentation.toCollisionData_collision
    [MeasurableSpace Mode]
    {collision : ResonantThreeWaveMeasure Mode} {reference : Measure Mode}
    (representation : PointwiseCollisionRepresentation collision reference)
    (action : Mode -> Real) (mode : Mode) :
    representation.toCollisionData.collision action mode =
      representation.collisionVector action mode := by
  rfl

end PointwiseRepresentation

section FiniteAdapter

variable {Mode Triad : Type}

/-- On a finite mode space, the coefficient of a mode is the weak collision
slope against that mode's indicator test.  This is a canonical extraction
from the collision measure, not an independently supplied collision map. -/
def finiteCollisionData [MeasurableSpace Mode] [Fintype Mode]
    [DecidableEq Mode] (collision : ResonantThreeWaveMeasure Mode) :
    CollisionData Mode where
  omega := collision.frequency
  collision := fun action mode =>
    weakCollisionSlope collision
      (fun other => if other = mode then 1 else 0) action

@[simp] theorem finiteCollisionData_omega
    [MeasurableSpace Mode] [Fintype Mode] [DecidableEq Mode]
    (collision : ResonantThreeWaveMeasure Mode) (mode : Mode) :
    (finiteCollisionData collision).omega mode = collision.frequency mode := by
  rfl

@[simp] theorem finiteCollisionData_collision_apply
    [MeasurableSpace Mode] [Fintype Mode] [DecidableEq Mode]
    (collision : ResonantThreeWaveMeasure Mode)
    (action : Mode -> Real) (mode : Mode) :
    (finiteCollisionData collision).collision action mode =
      weakCollisionSlope collision
        (fun other => if other = mode then 1 else 0) action := by
  rfl

/-- The finite vector extracted from a resonant measure represents its entire
weak collision functional against arbitrary mode tests. -/
theorem finiteCollisionData_weighted_sum_eq_weakCollisionSlope
    [MeasurableSpace Mode] [MeasurableSingletonClass Mode]
    [Fintype Mode] [DecidableEq Mode]
    (collision : ResonantThreeWaveMeasure Mode)
    (test action : Mode -> Real) :
    (∑ mode, test mode * (finiteCollisionData collision).collision action mode) =
      weakCollisionSlope collision test action := by
  unfold finiteCollisionData weakCollisionSlope
  simp only
  simp_rw [← integral_const_mul]
  rw [← integral_finsetSum Finset.univ]
  · apply integral_congr_ae
    filter_upwards with triad
    unfold triadWeakObservableIntegrand
    let flux := ThreeWaveCollisionAlgebra.collisionFlux
      (action (triad 0)) (action (triad 1)) (action (triad 2))
    change
      (∑ mode, test mode *
        (flux *
          ((if triad 0 = mode then 1 else 0) -
            (if triad 1 = mode then 1 else 0) -
            (if triad 2 = mode then 1 else 0)))) =
        flux * (test (triad 0) - test (triad 1) - test (triad 2))
    calc
      _ = flux *
          (∑ mode,
            (test mode * (if triad 0 = mode then 1 else 0) -
              test mode * (if triad 1 = mode then 1 else 0) -
              test mode * (if triad 2 = mode then 1 else 0))) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro mode _hmode
        ring
      _ = flux *
          ((∑ mode, test mode * (if triad 0 = mode then 1 else 0)) -
            (∑ mode, test mode * (if triad 1 = mode then 1 else 0)) -
            (∑ mode, test mode * (if triad 2 = mode then 1 else 0))) := by
        rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
      _ = _ := by simp
  · intro mode _hmode
    exact Integrable.of_finite

/-- Finite counting measure makes the canonical coordinate extraction a
proof-carrying pointwise representation of the entire weak functional. -/
def finitePointwiseCollisionRepresentation
    [MeasurableSpace Mode] [MeasurableSingletonClass Mode]
    [Fintype Mode] [DecidableEq Mode]
    (collision : ResonantThreeWaveMeasure Mode) :
    PointwiseCollisionRepresentation collision Measure.count where
  collisionVector := (finiteCollisionData collision).collision
  integrable_output := by
    intro _test _action _hintegrable
    exact Integrable.of_finite
  represents := by
    intro test action _hintegrable
    rw [MeasureTheory.integral_count]
    exact finiteCollisionData_weighted_sum_eq_weakCollisionSlope
      collision test action

/-- The generic collision data carried by the finite proof-carrying
representation is exactly the direct coordinate extraction. -/
theorem finitePointwiseCollisionRepresentation_toCollisionData_eq
    [MeasurableSpace Mode] [MeasurableSingletonClass Mode]
    [Fintype Mode] [DecidableEq Mode]
    (collision : ResonantThreeWaveMeasure Mode) :
    (finitePointwiseCollisionRepresentation collision).toCollisionData =
      finiteCollisionData collision := by
  rfl

/-- For an exact finite network, extracting coordinate collision slopes from
its atomic resonant measure recovers the original network vector field mode by
mode. -/
theorem finiteCollisionData_ofFiniteNetwork_collision_apply
    [MeasurableSpace Mode] [MeasurableSingletonClass Mode]
    [Fintype Mode] [DecidableEq Mode] [Fintype Triad]
    (network : Network Mode Triad) (frequency : Mode -> Real)
    (rate : Triad -> Real) (measurable_frequency : Measurable frequency)
    (rate_nonneg : forall a, 0 <= rate a)
    (resonance : forall a, frequency (network.mode₁ a) =
      frequency (network.mode₂ a) + frequency (network.mode₃ a))
    (action : Mode -> Real) (mode : Mode) :
    (finiteCollisionData
      (ofFiniteNetwork network frequency rate measurable_frequency
        rate_nonneg resonance)).collision action mode =
      collisionVectorField network rate action mode := by
  calc
    (finiteCollisionData
        (ofFiniteNetwork network frequency rate measurable_frequency
          rate_nonneg resonance)).collision action mode =
        weakCollisionSlope
          (ofFiniteNetwork network frequency rate measurable_frequency
            rate_nonneg resonance)
          (fun other => if other = mode then 1 else 0) action := rfl
    _ = weightedObservableSlope network
          (fun other => if other = mode then 1 else 0) rate action :=
      weakCollisionSlope_ofFiniteNetwork_eq_weightedObservableSlope
        network frequency (fun other => if other = mode then 1 else 0)
        action rate measurable_frequency rate_nonneg resonance
    _ = collisionVectorField network rate action mode := by
      unfold weightedObservableSlope
      simp

/-- The complete finite `CollisionData` recovered from the atomic resonance
measure is exactly the existing finite-network `CollisionData`. -/
theorem finiteCollisionData_ofFiniteNetwork_eq_networkCollisionData
    [MeasurableSpace Mode] [MeasurableSingletonClass Mode]
    [Fintype Mode] [DecidableEq Mode] [Fintype Triad]
    (network : Network Mode Triad) (frequency : Mode -> Real)
    (rate : Triad -> Real) (measurable_frequency : Measurable frequency)
    (rate_nonneg : forall a, 0 <= rate a)
    (resonance : forall a, frequency (network.mode₁ a) =
      frequency (network.mode₂ a) + frequency (network.mode₃ a)) :
    finiteCollisionData
      (ofFiniteNetwork network frequency rate measurable_frequency
        rate_nonneg resonance) =
      networkCollisionData network frequency rate := by
  unfold finiteCollisionData networkCollisionData
  apply congrArg (CollisionData.mk frequency)
  funext action mode
  exact finiteCollisionData_ofFiniteNetwork_collision_apply
    network frequency rate measurable_frequency rate_nonneg resonance action mode

/-- A finite resonant measure enters the existing strong finite wave-kinetic
ODE only through the canonically extracted collision data. -/
def SolvesFiniteResonantMeasureKineticEquation
    [MeasurableSpace Mode] [Fintype Mode] [DecidableEq Mode]
    (collision : ResonantThreeWaveMeasure Mode) (g : Real)
    (initial : Mode -> Real) (D : Real -> Mode -> Real) : Prop :=
  SolvesWaveKineticEquation (finiteCollisionData collision) g initial D

/-- For an atomic exact-resonance network, the measure-derived finite kinetic
equation is definitionally the same equation used by the existing F2 finite
network pipeline. -/
theorem solvesFiniteResonantMeasureKineticEquation_ofFiniteNetwork_iff
    [MeasurableSpace Mode] [MeasurableSingletonClass Mode]
    [Fintype Mode] [DecidableEq Mode] [Fintype Triad]
    (network : Network Mode Triad) (frequency : Mode -> Real)
    (rate : Triad -> Real) (measurable_frequency : Measurable frequency)
    (rate_nonneg : forall a, 0 <= rate a)
    (resonance : forall a, frequency (network.mode₁ a) =
      frequency (network.mode₂ a) + frequency (network.mode₃ a))
    (g : Real) (initial : Mode -> Real) (D : Real -> Mode -> Real) :
    SolvesFiniteResonantMeasureKineticEquation
        (ofFiniteNetwork network frequency rate measurable_frequency
          rate_nonneg resonance) g initial D ↔
      SolvesWaveKineticEquation
        (networkCollisionData network frequency rate) g initial D := by
  unfold SolvesFiniteResonantMeasureKineticEquation
  rw [finiteCollisionData_ofFiniteNetwork_eq_networkCollisionData]

end FiniteAdapter

end

end ArchonPhysics.ResonantThreeWaveKineticBridge
