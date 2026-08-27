import ArchonPhysics.FreeFPUTCounterrotatingFiniteTimeDecay

/-!
# Consumer: finite-time counterrotating three-wave decay

These endpoints expose the exact finite-volume nonresonance estimate used to
remove the all-plus and all-minus counterrotating three-wave sectors.  Their
constant uses the observed frequency itself and is not asserted to be
uniform in the lattice size.
-/

namespace ArchonPhysicsConsumers.Thermalization

open ArchonPhysics
open ArchonPhysics.FiniteTimeResonanceWeight
open ArchonPhysics.FreeFPUTCounterrotatingFiniteTimeDecay
open ArchonPhysics.FreeFPUTMismatchPhaseExpansion
open ArchonPhysics.FreeFPUTTensorPhaseExpansion
open ArchonPhysics.MicroscopicFiniteTimeCollisionPolynomial
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.NormalizedModeCoupling

noncomputable section

/-- The two-conjugate FPUT sector has an observed-frequency mismatch gap. -/
theorem problem_counterrotating_quadratic_mismatch_gap
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N)
    (inputModes : Fin 2 → Lattice.Site N) :
    modeFrequency m observed ≤
      |quadraticPhaseMismatch (modeFrequency m) observed
        (counterrotatingQuadraticPhaseTerm inputModes)| :=
  modeFrequency_observed_le_abs_quadraticPhaseMismatch_counterrotating
    m observed inputModes

/-- Its finite-time resonance weight is explicitly `O(1 / T)`. -/
theorem problem_counterrotating_quadratic_resonance_weight_le
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N)
    (inputModes : Fin 2 → Lattice.Site N) {T : Real}
    (hT : 0 < T) (hObserved : 0 < modeFrequency m observed) :
    finiteTimeResonanceWeight
        (quadraticPhaseMismatch (modeFrequency m) observed
          (counterrotatingQuadraticPhaseTerm inputModes)) T ≤
      (2 / modeFrequency m observed) ^ 2 / T :=
  finiteTimeResonanceWeight_quadraticCounterrotating_le
    m observed inputModes hT hObserved

/-- The complete fixed-output all-plus kernel sector obeys the same decay
with a finite static vertex constant. -/
theorem problem_counterrotating_threeWaveKernelSum_le
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (coupling : Real) (observed : Lattice.Site N) {T : Real}
    (hT : 0 < T) (hObserved : 0 < modeFrequency m observed) :
    counterrotatingThreeWaveKernelSum m coupling T observed ≤
      counterrotatingThreeWaveStaticVertexMass m coupling observed *
        ((2 / modeFrequency m observed) ^ 2 / T) :=
  counterrotatingThreeWaveKernelSum_le
    m coupling observed hT hObserved

/-- Global sign reversal gives the all-minus counterrotating estimate. -/
theorem problem_reverseCounterrotating_threeWaveKernelSum_le
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (coupling : Real) (observed : Lattice.Site N) {T : Real}
    (hT : 0 < T) (hObserved : 0 < modeFrequency m observed) :
    reverseCounterrotatingThreeWaveKernelSum m coupling T observed ≤
      counterrotatingThreeWaveStaticVertexMass m coupling observed *
        ((2 / modeFrequency m observed) ^ 2 / T) :=
  reverseCounterrotatingThreeWaveKernelSum_le
    m coupling observed hT hObserved

/-- For nonnegative modal actions, the full all-plus diagonal gain is also
bounded by an explicit fixed-volume `O(1 / T)` expression. -/
theorem problem_counterrotating_threeWaveActionSum_le
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (coupling : Real) (action : Lattice.Site N → Real)
    (observed : Lattice.Site N) {T : Real}
    (hT : 0 < T) (hObserved : 0 < modeFrequency m observed)
    (hAction : ∀ mode, 0 ≤ action mode) :
    counterrotatingThreeWaveActionSum m coupling T action observed ≤
      counterrotatingThreeWaveStaticActionMass m coupling action observed *
        ((2 / modeFrequency m observed) ^ 2 / T) :=
  counterrotatingThreeWaveActionSum_le
    m coupling action observed hT hObserved hAction

#print axioms problem_counterrotating_quadratic_mismatch_gap
#print axioms problem_counterrotating_quadratic_resonance_weight_le
#print axioms problem_counterrotating_threeWaveKernelSum_le
#print axioms problem_reverseCounterrotating_threeWaveKernelSum_le
#print axioms problem_counterrotating_threeWaveActionSum_le

end

end ArchonPhysicsConsumers.Thermalization
