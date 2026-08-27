import ArchonPhysics.FreeFPUTQuadraticCollisionKernelBridge
import ArchonPhysics.UniformOffResonanceDecay

/-!
# Finite-time decay of counterrotating three-wave sectors

The output convention in the free quadratic FPUT expansion fixes the
observed leg to have positive interaction sign.  When both input characters
are conjugate characters, all three collision signs are positive.  Its
frequency mismatch is therefore

`omega_observed + omega_input0 + omega_input1`.

Since harmonic frequencies are nonnegative, a strictly positive observed
frequency supplies an explicit gap for this counterrotating sector.  The
standard finite-time oscillatory estimate then gives a tuplewise and a
finite-sum `O(1 / T)` bound.  Global sign reversal supplies the corresponding
all-minus estimate.

The gap used below is exactly the observed frequency.  In particular, no
lower bound uniform in the volume `N` is assumed or concluded; the constants
are allowed to deteriorate for acoustic observed modes.
-/

namespace ArchonPhysics.FreeFPUTCounterrotatingFiniteTimeDecay

open ArchonPhysics
open ArchonPhysics.FinitePhaseMonomials
open ArchonPhysics.FiniteTimeResonanceWeight
open ArchonPhysics.FreeFPUTCollisionMismatchBridge
open ArchonPhysics.FreeFPUTMismatchPhaseExpansion
open ArchonPhysics.FreeFPUTQuadraticCollisionKernelBridge
open ArchonPhysics.FreeFPUTTensorPhaseExpansion
open ArchonPhysics.MicroscopicFiniteTimeCollisionPolynomial
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.NormalizedModeCoupling
open ArchonPhysics.UniformOffResonanceDecay

noncomputable section

/-- The all-plus three-wave sign pattern.  This is the counterrotating sector
in the output-plus convention of the quadratic FPUT equation. -/
def counterrotatingThreeWaveSign : Fin 3 → InteractionSign :=
  fun _ ↦ .plus

/-- The globally reversed all-minus counterrotating sign pattern. -/
def reverseCounterrotatingThreeWaveSign : Fin 3 → InteractionSign :=
  reverseSignPattern counterrotatingThreeWaveSign

@[simp] theorem counterrotatingThreeWaveSign_apply (r : Fin 3) :
    counterrotatingThreeWaveSign r = .plus := rfl

@[simp] theorem reverseCounterrotatingThreeWaveSign_apply (r : Fin 3) :
    reverseCounterrotatingThreeWaveSign r = .minus := by
  simp [reverseCounterrotatingThreeWaveSign, reverseSignPattern,
    counterrotatingThreeWaveSign, oppositeSign]

/-- The all-plus mismatch is the sum of the three nonnegative frequencies. -/
theorem phaseMismatch_counterrotatingThreeWaveSign
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (modes : ModeTuple N 3) :
    phaseMismatch m counterrotatingThreeWaveSign modes =
      modeFrequency m (modes 0) + modeFrequency m (modes 1) +
        modeFrequency m (modes 2) := by
  simp [phaseMismatch, counterrotatingThreeWaveSign, Fin.sum_univ_three]

/-- Global sign reversal negates the all-plus frequency sum. -/
theorem phaseMismatch_reverseCounterrotatingThreeWaveSign
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (modes : ModeTuple N 3) :
    phaseMismatch m reverseCounterrotatingThreeWaveSign modes =
      -(modeFrequency m (modes 0) + modeFrequency m (modes 1) +
        modeFrequency m (modes 2)) := by
  rw [reverseCounterrotatingThreeWaveSign,
    phaseMismatch_reverseSignPattern,
    phaseMismatch_counterrotatingThreeWaveSign]

/-- In the all-plus sector the zeroth-leg frequency is a lower bound for the
absolute mismatch.  No volume-uniform lower bound is hidden here. -/
theorem modeFrequency_le_abs_phaseMismatch_counterrotating
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (modes : ModeTuple N 3) :
    modeFrequency m (modes 0) ≤
      |phaseMismatch m counterrotatingThreeWaveSign modes| := by
  rw [phaseMismatch_counterrotatingThreeWaveSign]
  have hzero := modeFrequency_nonneg m (modes 0)
  have hone := modeFrequency_nonneg m (modes 1)
  have htwo := modeFrequency_nonneg m (modes 2)
  rw [abs_of_nonneg (by linarith)]
  linarith

/-- The same explicit zeroth-leg gap controls the globally reversed
all-minus sector. -/
theorem modeFrequency_le_abs_phaseMismatch_reverseCounterrotating
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (modes : ModeTuple N 3) :
    modeFrequency m (modes 0) ≤
      |phaseMismatch m reverseCounterrotatingThreeWaveSign modes| := by
  rw [reverseCounterrotatingThreeWaveSign,
    phaseMismatch_reverseSignPattern, abs_neg]
  exact modeFrequency_le_abs_phaseMismatch_counterrotating m modes

/-- Tuplewise `O(1 / T)` resonance-weight bound for the all-plus sector,
using the observed (zeroth-leg) frequency as the transparent gap. -/
theorem finiteTimeResonanceWeight_counterrotating_le
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (modes : ModeTuple N 3) {T : Real} (hT : 0 < T)
    (hObserved : 0 < modeFrequency m (modes 0)) :
    finiteTimeResonanceWeight
        (phaseMismatch m counterrotatingThreeWaveSign modes) T ≤
      (2 / modeFrequency m (modes 0)) ^ 2 / T := by
  exact finiteTimeResonanceWeight_le_inverseThreshold
    hT hObserved
      (modeFrequency_le_abs_phaseMismatch_counterrotating m modes)

/-- Tuplewise resonance-weight bound for the globally reversed all-minus
sector. -/
theorem finiteTimeResonanceWeight_reverseCounterrotating_le
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (modes : ModeTuple N 3) {T : Real} (hT : 0 < T)
    (hObserved : 0 < modeFrequency m (modes 0)) :
    finiteTimeResonanceWeight
        (phaseMismatch m reverseCounterrotatingThreeWaveSign modes) T ≤
      (2 / modeFrequency m (modes 0)) ^ 2 / T := by
  exact finiteTimeResonanceWeight_le_inverseThreshold
    hT hObserved
      (modeFrequency_le_abs_phaseMismatch_reverseCounterrotating m modes)

/-- Tuplewise collision-kernel bound for the all-plus counterrotating sector. -/
theorem finiteTimeCollisionKernel_counterrotating_le
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (coupling : Real) (modes : ModeTuple N 3) {T : Real}
    (hT : 0 < T) (hObserved : 0 < modeFrequency m (modes 0)) :
    finiteTimeCollisionKernel m coupling counterrotatingThreeWaveSign T modes ≤
      (coupling ^ 2 * normalizedInteractionWeight m modes) *
        ((2 / modeFrequency m (modes 0)) ^ 2 / T) := by
  unfold finiteTimeCollisionKernel hamiltonianInteractionVertex
  rw [mul_pow, normalizedInteractionVertex_sq]
  exact mul_le_mul_of_nonneg_left
    (finiteTimeResonanceWeight_counterrotating_le
      m modes hT hObserved)
    (mul_nonneg (sq_nonneg coupling)
      (normalizedInteractionWeight_nonneg m modes))

/-- Tuplewise collision-kernel bound for the all-minus counterrotating
sector. -/
theorem finiteTimeCollisionKernel_reverseCounterrotating_le
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (coupling : Real) (modes : ModeTuple N 3) {T : Real}
    (hT : 0 < T) (hObserved : 0 < modeFrequency m (modes 0)) :
    finiteTimeCollisionKernel m coupling
        reverseCounterrotatingThreeWaveSign T modes ≤
      (coupling ^ 2 * normalizedInteractionWeight m modes) *
        ((2 / modeFrequency m (modes 0)) ^ 2 / T) := by
  unfold finiteTimeCollisionKernel hamiltonianInteractionVertex
  rw [mul_pow, normalizedInteractionVertex_sq]
  exact mul_le_mul_of_nonneg_left
    (finiteTimeResonanceWeight_reverseCounterrotating_le
      m modes hT hObserved)
    (mul_nonneg (sq_nonneg coupling)
      (normalizedInteractionWeight_nonneg m modes))

/-- The quadratic FPUT term with two conjugate input characters. -/
def counterrotatingQuadraticPhaseTerm {N : Nat}
    (inputModes : Fin 2 → Lattice.Site N) : QuadraticPhaseTerm N :=
  (inputModes, (1, 1))

@[simp] theorem counterrotatingQuadraticPhaseTerm_modes
    {N : Nat} (inputModes : Fin 2 → Lattice.Site N) :
    (counterrotatingQuadraticPhaseTerm inputModes).1 = inputModes := rfl

@[simp] theorem counterrotatingQuadraticPhaseTerm_leftSign
    {N : Nat} (inputModes : Fin 2 → Lattice.Site N) :
    (counterrotatingQuadraticPhaseTerm inputModes).2.1 = 1 := rfl

@[simp] theorem counterrotatingQuadraticPhaseTerm_rightSign
    {N : Nat} (inputModes : Fin 2 → Lattice.Site N) :
    (counterrotatingQuadraticPhaseTerm inputModes).2.2 = 1 := rfl

/-- Two conjugate input characters give exactly the all-plus collision sign
pattern. -/
theorem quadraticCollisionSign_counterrotatingQuadraticPhaseTerm
    {N : Nat} [NeZero N] (inputModes : Fin 2 → Lattice.Site N) :
    quadraticCollisionSign (counterrotatingQuadraticPhaseTerm inputModes) =
      counterrotatingThreeWaveSign := by
  funext r
  fin_cases r <;> rfl

/-- The collision modes are the observed leg followed by the supplied input
modes. -/
@[simp] theorem quadraticCollisionModes_counterrotatingQuadraticPhaseTerm
    {N : Nat} [NeZero N] (observed : Lattice.Site N)
    (inputModes : Fin 2 → Lattice.Site N) :
    quadraticCollisionModes observed
        (counterrotatingQuadraticPhaseTerm inputModes) =
      Fin.cons observed inputModes := rfl

/-- The exact FPUT mismatch in the two-conjugate sector is the positive sum
of observed and input frequencies. -/
theorem quadraticPhaseMismatch_counterrotatingQuadraticPhaseTerm
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N)
    (inputModes : Fin 2 → Lattice.Site N) :
    quadraticPhaseMismatch (modeFrequency m) observed
        (counterrotatingQuadraticPhaseTerm inputModes) =
      modeFrequency m observed + modeFrequency m (inputModes 0) +
        modeFrequency m (inputModes 1) := by
  rw [quadraticPhaseMismatch_modeFrequency_eq_phaseMismatch,
    quadraticCollisionSign_counterrotatingQuadraticPhaseTerm,
    quadraticCollisionModes_counterrotatingQuadraticPhaseTerm,
    phaseMismatch_counterrotatingThreeWaveSign]
  rfl

/-- The observed frequency is an explicit lower bound for the absolute FPUT
counterrotating mismatch. -/
theorem modeFrequency_observed_le_abs_quadraticPhaseMismatch_counterrotating
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N)
    (inputModes : Fin 2 → Lattice.Site N) :
    modeFrequency m observed ≤
      |quadraticPhaseMismatch (modeFrequency m) observed
        (counterrotatingQuadraticPhaseTerm inputModes)| := by
  rw [quadraticPhaseMismatch_modeFrequency_eq_phaseMismatch,
    quadraticCollisionSign_counterrotatingQuadraticPhaseTerm,
    quadraticCollisionModes_counterrotatingQuadraticPhaseTerm]
  exact modeFrequency_le_abs_phaseMismatch_counterrotating
    m (Fin.cons observed inputModes)

/-- FPUT termwise finite-time resonance bound in the two-conjugate sector. -/
theorem finiteTimeResonanceWeight_quadraticCounterrotating_le
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N)
    (inputModes : Fin 2 → Lattice.Site N) {T : Real}
    (hT : 0 < T) (hObserved : 0 < modeFrequency m observed) :
    finiteTimeResonanceWeight
        (quadraticPhaseMismatch (modeFrequency m) observed
          (counterrotatingQuadraticPhaseTerm inputModes)) T ≤
      (2 / modeFrequency m observed) ^ 2 / T := by
  exact finiteTimeResonanceWeight_le_inverseThreshold hT hObserved
    (modeFrequency_observed_le_abs_quadraticPhaseMismatch_counterrotating
      m observed inputModes)

/-- Static fixed-output vertex mass appearing in the finite all-plus kernel
bound.  It is finite because the mode space is finite. -/
def counterrotatingThreeWaveStaticVertexMass
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (coupling : Real) (observed : Lattice.Site N) : Real :=
  ∑ inputModes : Fin 2 → Lattice.Site N,
    coupling ^ 2 * normalizedInteractionWeight m (Fin.cons observed inputModes)

/-- The complete fixed-output all-plus finite-time kernel sum. -/
def counterrotatingThreeWaveKernelSum
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (coupling T : Real) (observed : Lattice.Site N) : Real :=
  ∑ inputModes : Fin 2 → Lattice.Site N,
    finiteTimeCollisionKernel m coupling counterrotatingThreeWaveSign T
      (Fin.cons observed inputModes)

/-- The globally reversed all-minus fixed-output finite-time kernel sum. -/
def reverseCounterrotatingThreeWaveKernelSum
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (coupling T : Real) (observed : Lattice.Site N) : Real :=
  ∑ inputModes : Fin 2 → Lattice.Site N,
    finiteTimeCollisionKernel m coupling
      reverseCounterrotatingThreeWaveSign T (Fin.cons observed inputModes)

/-- Finite all-plus kernel sum bound with its exact fixed-volume static
constant. -/
theorem counterrotatingThreeWaveKernelSum_le
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (coupling : Real) (observed : Lattice.Site N) {T : Real}
    (hT : 0 < T) (hObserved : 0 < modeFrequency m observed) :
    counterrotatingThreeWaveKernelSum m coupling T observed ≤
      counterrotatingThreeWaveStaticVertexMass m coupling observed *
        ((2 / modeFrequency m observed) ^ 2 / T) := by
  classical
  unfold counterrotatingThreeWaveKernelSum
    counterrotatingThreeWaveStaticVertexMass
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro inputModes hInputModes
  exact finiteTimeCollisionKernel_counterrotating_le
    m coupling (Fin.cons observed inputModes) hT hObserved

/-- The same finite-sum bound holds after global sign reversal. -/
theorem reverseCounterrotatingThreeWaveKernelSum_le
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (coupling : Real) (observed : Lattice.Site N) {T : Real}
    (hT : 0 < T) (hObserved : 0 < modeFrequency m observed) :
    reverseCounterrotatingThreeWaveKernelSum m coupling T observed ≤
      counterrotatingThreeWaveStaticVertexMass m coupling observed *
        ((2 / modeFrequency m observed) ^ 2 / T) := by
  classical
  unfold reverseCounterrotatingThreeWaveKernelSum
    counterrotatingThreeWaveStaticVertexMass
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro inputModes hInputModes
  exact finiteTimeCollisionKernel_reverseCounterrotating_le
    m coupling (Fin.cons observed inputModes) hT hObserved

/-- Fixed-output all-plus kernel sum weighted by the two input actions. -/
def counterrotatingThreeWaveActionSum
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (coupling T : Real) (action : Lattice.Site N → Real)
    (observed : Lattice.Site N) : Real :=
  ∑ inputModes : Fin 2 → Lattice.Site N,
    finiteTimeCollisionKernel m coupling counterrotatingThreeWaveSign T
        (Fin.cons observed inputModes) *
      ∏ r : Fin 2, action (inputModes r)

/-- The corresponding static action-weighted vertex mass. -/
def counterrotatingThreeWaveStaticActionMass
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (coupling : Real) (action : Lattice.Site N → Real)
    (observed : Lattice.Site N) : Real :=
  ∑ inputModes : Fin 2 → Lattice.Site N,
    (coupling ^ 2 *
        normalizedInteractionWeight m (Fin.cons observed inputModes)) *
      ∏ r : Fin 2, action (inputModes r)

/-- The full fixed-output counterrotating diagonal gain has an explicit
`O(1 / T)` bound for every nonnegative action profile. -/
theorem counterrotatingThreeWaveActionSum_le
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (coupling : Real) (action : Lattice.Site N → Real)
    (observed : Lattice.Site N) {T : Real}
    (hT : 0 < T) (hObserved : 0 < modeFrequency m observed)
    (hAction : ∀ mode, 0 ≤ action mode) :
    counterrotatingThreeWaveActionSum m coupling T action observed ≤
      counterrotatingThreeWaveStaticActionMass m coupling action observed *
        ((2 / modeFrequency m observed) ^ 2 / T) := by
  classical
  unfold counterrotatingThreeWaveActionSum
    counterrotatingThreeWaveStaticActionMass
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro inputModes hInputModes
  have hProduct : 0 ≤ ∏ r : Fin 2, action (inputModes r) :=
    Finset.prod_nonneg fun r hr ↦ hAction (inputModes r)
  calc
    finiteTimeCollisionKernel m coupling counterrotatingThreeWaveSign T
          (Fin.cons observed inputModes) *
        ∏ r : Fin 2, action (inputModes r) ≤
        ((coupling ^ 2 *
            normalizedInteractionWeight m (Fin.cons observed inputModes)) *
          ((2 / modeFrequency m observed) ^ 2 / T)) *
            ∏ r : Fin 2, action (inputModes r) :=
      mul_le_mul_of_nonneg_right
        (finiteTimeCollisionKernel_counterrotating_le
          m coupling (Fin.cons observed inputModes) hT hObserved)
        hProduct
    _ = (coupling ^ 2 *
            normalizedInteractionWeight m (Fin.cons observed inputModes)) *
          (∏ r : Fin 2, action (inputModes r)) *
            ((2 / modeFrequency m observed) ^ 2 / T) := by ring

end

end ArchonPhysics.FreeFPUTCounterrotatingFiniteTimeDecay
