import ArchonPhysics.FiniteThreeWaveCollisionNetwork
import Mathlib.MeasureTheory.Measure.FiniteMeasure
import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Resonant three-wave measures

This module gives one weak-form interface shared by continuum collision
measures and finite atomic collision networks.  A resonant measure records a
measurable mode frequency, a finite measure on ordered three-mode tuples, and
the additive resonance relation almost everywhere.  No permutation or child
symmetry is included in the interface.

For a finite collision network, a nonnegative rate is absorbed into the mass
of a Dirac atom at each ordered triad.  The resulting weak collision slope is
exactly the existing finite-network weighted-observable slope.
-/

namespace ArchonPhysics

open MeasureTheory

noncomputable section

/-- A finite measure on ordered three-mode collisions, supported almost
everywhere on the additive resonance surface `omega_1 = omega_2 + omega_3`.
No symmetry between the two child legs is assumed. -/
structure ResonantThreeWaveMeasure (Mode : Type*) [MeasurableSpace Mode] where
  frequency : Mode -> Real
  measurable_frequency : Measurable frequency
  collisionMeasure : FiniteMeasure (Fin 3 -> Mode)
  resonance_ae :
    ∀ᵐ ae_triad ∂(collisionMeasure : Measure (Fin 3 -> Mode)),
      frequency (ae_triad 0) =
        frequency (ae_triad 1) + frequency (ae_triad 2)

namespace ResonantThreeWaveMeasure

open FiniteThreeWaveCollisionNetwork
open ThreeWaveCollisionAlgebra

variable {Mode Triad : Type*}

/-- The weak contribution of one ordered triad to a linear mode observable.
The collision rate is not present here: for a collision measure it is part of
the measure's mass. -/
def triadWeakObservableIntegrand
    (test action : Mode -> Real) (triad : Fin 3 -> Mode) : Real :=
  collisionFlux (action (triad 0)) (action (triad 1)) (action (triad 2)) *
    (test (triad 0) - test (triad 1) - test (triad 2))

/-- Weak collision slope of a supplied linear test observable. -/
def weakCollisionSlope
    [MeasurableSpace Mode]
    (collision : ResonantThreeWaveMeasure Mode)
    (test action : Mode -> Real) : Real :=
  ∫ triad, triadWeakObservableIntegrand test action triad
    ∂collision.collisionMeasure

/-- Ordered mode triple associated with a finite-network triad. -/
def networkTriad (network : Network Mode Triad) (a : Triad) : Fin 3 -> Mode :=
  fun r => Fin.cases (network.mode₁ a)
    (fun r' => Fin.cases (network.mode₂ a)
      (fun _ => network.mode₃ a) r') r

@[simp] theorem networkTriad_zero
    (network : Network Mode Triad) (a : Triad) :
    networkTriad network a 0 = network.mode₁ a := by
  rfl

@[simp] theorem networkTriad_one
    (network : Network Mode Triad) (a : Triad) :
    networkTriad network a 1 = network.mode₂ a := by
  rfl

@[simp] theorem networkTriad_two
    (network : Network Mode Triad) (a : Triad) :
    networkTriad network a 2 = network.mode₃ a := by
  rfl

/-- Finite atomic collision measure of a network.  The supplied proof of rate
nonnegativity makes each real rate an `NNReal` mass, so no truncation occurs. -/
def atomicCollisionMeasure [MeasurableSpace Mode] [Fintype Triad]
    (network : Network Mode Triad) (rate : Triad -> Real)
    (_rate_nonneg : forall a, 0 <= rate a) :
    FiniteMeasure (Fin 3 -> Mode) := by
  classical
  refine ⟨∑ a,
    ENNReal.ofReal (rate a) •
      Measure.dirac (networkTriad network a), ?_⟩
  constructor
  simp only [Measure.coe_finsetSum, Finset.sum_apply, ENNReal.sum_lt_top,
    Finset.mem_univ, forall_const]
  intro a
  simp

/-- A finite exact-resonance network produces a resonant atomic measure.  Its
only structural support condition is additive frequency resonance. -/
def ofFiniteNetwork [MeasurableSpace Mode] [Fintype Triad]
    [MeasurableSingletonClass Mode]
    (network : Network Mode Triad) (frequency : Mode -> Real)
    (rate : Triad -> Real) (measurable_frequency : Measurable frequency)
    (rate_nonneg : forall a, 0 <= rate a)
    (resonance : forall a, frequency (network.mode₁ a) =
      frequency (network.mode₂ a) + frequency (network.mode₃ a)) :
    ResonantThreeWaveMeasure Mode where
  frequency := frequency
  measurable_frequency := measurable_frequency
  collisionMeasure := atomicCollisionMeasure network rate rate_nonneg
  resonance_ae := by
    unfold atomicCollisionMeasure
    simp only [FiniteMeasure.toMeasure_mk]
    rw [← Measure.sum_fintype, Measure.ae_sum_iff]
    intro a
    apply Measure.ae_smul_measure
    simpa only [ae_dirac_eq, Filter.eventually_pure, networkTriad_zero, networkTriad_one,
      networkTriad_two] using resonance a

/-- Integrating against the atomic network measure recovers the sum of
single-triad observable slopes. -/
theorem weakCollisionSlope_ofFiniteNetwork_eq_sum
    [MeasurableSpace Mode] [Fintype Triad] [MeasurableSingletonClass Mode]
    (network : Network Mode Triad) (frequency test action : Mode -> Real)
    (rate : Triad -> Real) (measurable_frequency : Measurable frequency)
    (rate_nonneg : forall a, 0 <= rate a)
    (resonance : forall a, frequency (network.mode₁ a) =
      frequency (network.mode₂ a) + frequency (network.mode₃ a)) :
    weakCollisionSlope
        (ofFiniteNetwork network frequency rate measurable_frequency
          rate_nonneg resonance)
        test action =
      ∑ a, linearObservableSlope
        (test (network.mode₁ a))
        (test (network.mode₂ a))
        (test (network.mode₃ a))
        (rate a)
        (action (network.mode₁ a))
        (action (network.mode₂ a))
        (action (network.mode₃ a)) := by
  unfold weakCollisionSlope ofFiniteNetwork atomicCollisionMeasure
  rw [FiniteMeasure.toMeasure_mk, integral_finsetSum_measure]
  · apply Finset.sum_congr rfl
    intro a _
    rw [integral_smul_measure, integral_dirac]
    rw [ENNReal.toReal_ofReal (rate_nonneg a)]
    unfold triadWeakObservableIntegrand linearObservableSlope
    simp only [smul_eq_mul, networkTriad_zero, networkTriad_one, networkTriad_two]
    ring
  · intro a _
    exact (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top

/-- The atomic weak-form construction is definitionally compatible with the
existing per-mode finite-network collision vector field. -/
theorem weakCollisionSlope_ofFiniteNetwork_eq_weightedObservableSlope
    [MeasurableSpace Mode] [Fintype Mode] [DecidableEq Mode] [Fintype Triad]
    [MeasurableSingletonClass Mode]
    (network : Network Mode Triad) (frequency test action : Mode -> Real)
    (rate : Triad -> Real) (measurable_frequency : Measurable frequency)
    (rate_nonneg : forall a, 0 <= rate a)
    (resonance : forall a, frequency (network.mode₁ a) =
      frequency (network.mode₂ a) + frequency (network.mode₃ a)) :
    weakCollisionSlope
        (ofFiniteNetwork network frequency rate measurable_frequency
          rate_nonneg resonance)
        test action =
      weightedObservableSlope network test rate action := by
  rw [weakCollisionSlope_ofFiniteNetwork_eq_sum]
  exact (weightedObservableSlope_eq_sum network test rate action).symm

/-- Additive resonance makes frequency a collision invariant for every
resonant finite measure, without any permutation-symmetry hypothesis. -/
theorem weakCollisionSlope_frequency_eq_zero
    [MeasurableSpace Mode]
    (collision : ResonantThreeWaveMeasure Mode) (action : Mode -> Real) :
    weakCollisionSlope collision collision.frequency action = 0 := by
  unfold weakCollisionSlope
  apply integral_eq_zero_of_ae
  filter_upwards [collision.resonance_ae] with triad hresonance
  have hzero : triadWeakObservableIntegrand collision.frequency action triad =
      (0 : Real) := by
    unfold triadWeakObservableIntegrand
    rw [hresonance]
    ring
  simpa only [Pi.zero_apply] using hzero

end ResonantThreeWaveMeasure

end

end ArchonPhysics
