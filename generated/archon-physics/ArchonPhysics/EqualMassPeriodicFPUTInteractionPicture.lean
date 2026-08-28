import ArchonPhysics.ComplexFourierBranchAmplitude
import ArchonPhysics.EqualMassPeriodicFPUTFourierHamiltonian
import ArchonPhysics.PhyslibHamiltonDerivativeBridge

/-!
# Exact interaction picture for equal-mass periodic alpha-FPUT

This module changes the exact finite-volume complex Fourier Hamilton equations
to signed positive/negative frequency branches and then removes their free
rotations.  Every formula is an identity for a differentiable Physlib
trajectory.  No random-phase, kinetic, resonant-shell, or limiting hypothesis
is used.
-/

namespace ArchonPhysics.EqualMassPeriodicFPUTInteractionPicture

open scoped BigOperators

open ArchonPhysics
open ArchonPhysics.CleanCycleAcousticCountEnvelope
open ArchonPhysics.CoerciveHamiltonianPhyslib
open ArchonPhysics.ComplexFourierBranchAmplitude
open ArchonPhysics.EqualMassPeriodicFPUTFourierHamiltonian
open ArchonPhysics.FinitePhaseMonomials
open ArchonPhysics.Lattice
open ArchonPhysics.PhaseRenormalization
open ArchonPhysics.PhyslibHamiltonDerivativeBridge
open Time

noncomputable section

/-! ## Positive acoustic frequency away from the translation mode -/

/-- Positive-branch clean-cycle frequency. -/
def equalMassFourierFrequency
    (N : Nat) [NeZero N] (k : Site N) : Real :=
  Real.sqrt (cleanCycleModeEnergy N k)

theorem equalMassFourierAngle_pos_of_ne_zero
    {N : Nat} [NeZero N] {k : Site N} (hk : k ≠ 0) :
    0 < Real.pi * (k.val : Real) / (N : Real) := by
  have hN : 0 < (N : Real) := by exact_mod_cast NeZero.pos N
  have hkval : 0 < k.val := Nat.pos_of_ne_zero (by
    intro hzero
    apply hk
    apply ZMod.val_injective N
    simp [hzero])
  positivity

theorem equalMassFourierAngle_lt_pi
    (N : Nat) [NeZero N] (k : Site N) :
    Real.pi * (k.val : Real) / (N : Real) < Real.pi := by
  have hN : 0 < (N : Real) := by exact_mod_cast NeZero.pos N
  have hklt : (k.val : Real) < (N : Real) := by exact_mod_cast k.val_lt
  have hratio : (k.val : Real) / (N : Real) < 1 :=
    (div_lt_one hN).2 hklt
  calc
    Real.pi * (k.val : Real) / (N : Real) =
        Real.pi * ((k.val : Real) / (N : Real)) := by ring
    _ < Real.pi * 1 := mul_lt_mul_of_pos_left hratio Real.pi_pos
    _ = Real.pi := by ring

theorem equalMassFourierFrequency_pos_of_ne_zero
    {N : Nat} [NeZero N] {k : Site N} (hk : k ≠ 0) :
    0 < equalMassFourierFrequency N k := by
  apply Real.sqrt_pos.mpr
  unfold cleanCycleModeEnergy
  have hsin : 0 < Real.sin
      (Real.pi * (k.val : Real) / (N : Real)) :=
    Real.sin_pos_of_pos_of_lt_pi
      (equalMassFourierAngle_pos_of_ne_zero hk)
      (equalMassFourierAngle_lt_pi N k)
  positivity

theorem equalMassFourierFrequency_sq
    (N : Nat) [NeZero N] (k : Site N) :
    equalMassFourierFrequency N k ^ 2 = cleanCycleModeEnergy N k := by
  exact Real.sq_sqrt (by
    unfold cleanCycleModeEnergy
    positivity)

/-! ## Real reparametrization of the exact Fourier trajectory -/

/-- Fourier position after the canonical `Time`-to-`Real` reparametrization. -/
def realFourierPosition
    {N : Nat} [NeZero N] (k : Site N)
    (q : Time → HilbertConfiguration N) : Real → Complex :=
  fun tau ↦ cycleFourierProjectionCLM N k
    (q (Time.toRealCLE.symm tau))

/-- Fourier momentum after the canonical `Time`-to-`Real` reparametrization. -/
def realFourierMomentum
    {N : Nat} [NeZero N] (k : Site N)
    (p : Time → HilbertConfiguration N) : Real → Complex :=
  fun tau ↦ cycleFourierProjectionCLM N k
    (p (Time.toRealCLE.symm tau))

/-- The exact Fourier Hamilton equations as `HasDerivAt` statements on the
real time coordinate. -/
theorem hasDerivAt_realFourierEquations
    {N : Nat} [NeZero N] (alpha : Real)
    (p q : Time → HilbertConfiguration N)
    (hHamilton :
      SatisfiesHamiltonEquations (unitMassConfig N) 1 0 alpha p q)
    (hp : Differentiable Real p) (hq : Differentiable Real q)
    (tau : Real) (k : Site N) :
    HasDerivAt (realFourierPosition k q)
      (realFourierMomentum k p tau) tau ∧
    HasDerivAt (realFourierMomentum k p)
      (-(cleanCycleModeEnergy N k : Complex) *
          realFourierPosition k q tau +
        ∑ l : Site N,
          pureAlphaQuadraticFourierCoefficient N alpha k l *
            realFourierPosition l q tau *
            realFourierPosition (k - l) q tau) tau := by
  let t : Time := Time.toRealCLE.symm tau
  have hmodal := pureAlpha_fourierModalEquations alpha p q hHamilton hp hq
  have hQdiff : DifferentiableAt Real
      (fun s : Time ↦ cycleFourierProjectionCLM N k (q s)) t :=
    (cycleFourierProjectionCLM N k).differentiableAt.comp t (hq t)
  have hPdiff : DifferentiableAt Real
      (fun s : Time ↦ cycleFourierProjectionCLM N k (p s)) t :=
    (cycleFourierProjectionCLM N k).differentiableAt.comp t (hp t)
  constructor
  · have hQ := hasDerivAt_comp_toRealCLE_symm
      (fun s : Time ↦ cycleFourierProjectionCLM N k (q s)) tau hQdiff
    rw [hmodal.1 t k] at hQ
    convert hQ using 1 <;> rfl
  · have hP := hasDerivAt_comp_toRealCLE_symm
      (fun s : Time ↦ cycleFourierProjectionCLM N k (p s)) tau hPdiff
    rw [hmodal.2 t k] at hP
    convert hP using 1 <;> rfl

/-! ## Safe removal of translation-mode inputs -/

/-- Input momenta for which both children have positive acoustic frequency. -/
def nonzeroInputMomenta
    (N : Nat) [NeZero N] (k : Site N) : Finset (Site N) :=
  Finset.univ.filter fun l ↦ l ≠ 0 ∧ k - l ≠ 0

@[simp] theorem mem_nonzeroInputMomenta
    {N : Nat} [NeZero N] {k l : Site N} :
    l ∈ nonzeroInputMomenta N k ↔ l ≠ 0 ∧ k - l ≠ 0 := by
  simp [nonzeroInputMomenta]

/-- The complete quadratic convolution equals its two-positive-input
restriction because every omitted term contains a zero bond symbol. -/
theorem fullQuadraticConvolution_eq_nonzeroInputs
    {N : Nat} [NeZero N] (alpha : Real) (k : Site N)
    (Q : Site N → Complex) :
    (∑ l : Site N,
        pureAlphaQuadraticFourierCoefficient N alpha k l *
          Q l * Q (k - l)) =
      ∑ l ∈ nonzeroInputMomenta N k,
        pureAlphaQuadraticFourierCoefficient N alpha k l *
          Q l * Q (k - l) := by
  rw [nonzeroInputMomenta, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro l _hl
  by_cases hleft : l = 0
  · subst l
    simp
  · by_cases hright : k - l = 0
    · have hcoefficient :
          pureAlphaQuadraticFourierCoefficient N alpha k l = 0 := by
          unfold pureAlphaQuadraticFourierCoefficient
          rw [hright]
          simp
      simp [hleft, hright, hcoefficient]
    · simp [hleft, hright]

/-- Exact modular momentum relation carried by every convolution summand. -/
theorem output_eq_left_add_right
    {N : Nat} [NeZero N] (k l : Site N) :
    k = l + (k - l) := by
  ring

/-! ## Signed branches and the exact interaction-picture source -/

/-- The explicit two-element set of frequency branches. -/
def phaseSignFinset : Finset PhaseSign :=
  {.phase, .conjugate}

@[simp] theorem mem_phaseSignFinset (sign : PhaseSign) :
    sign ∈ phaseSignFinset := by
  cases sign <;> simp [phaseSignFinset]

/-- The quadratic forcing after safely deleting its zero-frequency inputs. -/
def nonzeroQuadraticForcing
    {N : Nat} [NeZero N] (alpha : Real) (k : Site N)
    (Q : Site N → Real → Complex) (tau : Real) : Complex :=
  ∑ l ∈ nonzeroInputMomenta N k,
    pureAlphaQuadraticFourierCoefficient N alpha k l *
      Q l tau * Q (k - l) tau

/-- The signed interaction-picture path of one actual Fourier mode. -/
def equalMassInteractionBranch
    {N : Nat} [NeZero N] (sign : PhaseSign) (k : Site N)
    (p q : Time → HilbertConfiguration N) : Real → Complex :=
  complexFourierInteractionBranch (equalMassFourierFrequency N k) sign
    (realFourierPosition k q) (realFourierMomentum k p)

/-- Before expanding the two input coordinates into branches, an actual
Physlib trajectory already satisfies the exact signed interaction-picture
source equation. -/
theorem hasDerivAt_equalMassInteractionBranch_source
    {N : Nat} [NeZero N] (alpha : Real) (sign : PhaseSign) (k : Site N)
    (p q : Time → HilbertConfiguration N)
    (hHamilton :
      SatisfiesHamiltonEquations (unitMassConfig N) 1 0 alpha p q)
    (hp : Differentiable Real p) (hq : Differentiable Real q)
    (hk : k ≠ 0) (tau : Real) :
    HasDerivAt (equalMassInteractionBranch sign k p q)
      (phaseFactor
          (phaseSignReal sign * equalMassFourierFrequency N k * tau) *
        complexFourierBranchSource (equalMassFourierFrequency N k) sign
          (nonzeroQuadraticForcing alpha k
            (fun l ↦ realFourierPosition l q) tau)) tau := by
  have heq := hasDerivAt_realFourierEquations
    alpha p q hHamilton hp hq tau k
  have hrestricted := fullQuadraticConvolution_eq_nonzeroInputs
    alpha k (fun l ↦ realFourierPosition l q tau)
  rw [hrestricted] at heq
  have hmomentum : HasDerivAt (realFourierMomentum k p)
      (-((equalMassFourierFrequency N k) ^ 2 : Real) *
          realFourierPosition k q tau +
        nonzeroQuadraticForcing alpha k
          (fun l ↦ realFourierPosition l q) tau) tau := by
    convert heq.2 using 1
    · rw [equalMassFourierFrequency_sq]
      norm_cast
  simpa only [equalMassInteractionBranch] using
    hasDerivAt_complexFourierInteractionBranch
      (equalMassFourierFrequency_pos_of_ne_zero hk) sign heq.1 hmomentum

/-- Signed quadratic phase mismatch.  Unlike the older positive-output-only
mismatch, this definition is valid on both output branches. -/
def equalMassQuadraticBranchMismatch
    {N : Nat} [NeZero N] (k l : Site N)
    (outputSign leftSign rightSign : PhaseSign) : Real :=
  phaseSignReal outputSign * equalMassFourierFrequency N k -
    phaseSignReal leftSign * equalMassFourierFrequency N l -
    phaseSignReal rightSign * equalMassFourierFrequency N (k - l)

/-- Fully normalized signed vertex multiplying two interaction-picture input
branches.  The three square-root factors come respectively from the output
source and the two coordinate reconstructions. -/
def equalMassQuadraticBranchVertex
    {N : Nat} [NeZero N] (alpha : Real) (k l : Site N)
    (outputSign : PhaseSign) : Complex :=
  ((phaseSignReal outputSign : Complex) * Complex.I *
      pureAlphaQuadraticFourierCoefficient N alpha k l) /
    Real.sqrt (2 * equalMassFourierFrequency N k) /
    Real.sqrt (2 * equalMassFourierFrequency N l) /
    Real.sqrt (2 * equalMassFourierFrequency N (k - l))

/-- One explicit momentum-conserving, phase-mismatched branch summand. -/
def equalMassQuadraticBranchTerm
    {N : Nat} [NeZero N] (alpha : Real) (k l : Site N)
    (outputSign leftSign rightSign : PhaseSign)
    (p q : Time → HilbertConfiguration N) (tau : Real) : Complex :=
  phaseFactor
      (equalMassQuadraticBranchMismatch k l outputSign leftSign rightSign * tau) *
    equalMassQuadraticBranchVertex alpha k l outputSign *
    equalMassInteractionBranch leftSign l p q tau *
    equalMassInteractionBranch rightSign (k - l) p q tau

/-- One input-coordinate contribution reconstructed from an interaction
branch. -/
def equalMassBranchCoordinateTerm
    {N : Nat} [NeZero N] (sign : PhaseSign) (k : Site N)
    (p q : Time → HilbertConfiguration N) (tau : Real) : Complex :=
  phaseRenormalize
      (-(phaseSignReal sign * equalMassFourierFrequency N k * tau))
      (equalMassInteractionBranch sign k p q tau) /
    Real.sqrt (2 * equalMassFourierFrequency N k)

/-- Exact reconstruction of a nonzero Fourier coordinate as the sum of its
two interaction-picture branches. -/
theorem realFourierPosition_eq_branch_sum
    {N : Nat} [NeZero N] (k : Site N)
    (p q : Time → HilbertConfiguration N) (hk : k ≠ 0) (tau : Real) :
    realFourierPosition k q tau =
      ∑ sign ∈ phaseSignFinset,
        equalMassBranchCoordinateTerm sign k p q tau := by
  have h := coordinate_eq_interactionBranch_sum_div_sqrt
    (equalMassFourierFrequency_pos_of_ne_zero hk)
    (realFourierPosition k q) (realFourierMomentum k p) tau
  rw [h]
  simp [phaseSignFinset, equalMassBranchCoordinateTerm,
    equalMassInteractionBranch]
  ring

/-- Product of the output rotation and the two inverse input rotations is
the exponential of the displayed signed mismatch. -/
theorem phaseFactor_output_mul_inputs_eq_mismatch
    {N : Nat} [NeZero N] (k l : Site N)
    (outputSign leftSign rightSign : PhaseSign) (tau : Real) :
    phaseFactor
        (phaseSignReal outputSign * equalMassFourierFrequency N k * tau) *
      phaseFactor
        (-(phaseSignReal leftSign * equalMassFourierFrequency N l * tau)) *
      phaseFactor
        (-(phaseSignReal rightSign *
          equalMassFourierFrequency N (k - l) * tau)) =
      phaseFactor
        (equalMassQuadraticBranchMismatch k l
          outputSign leftSign rightSign * tau) := by
  unfold phaseFactor equalMassQuadraticBranchMismatch
  rw [← Complex.exp_add, ← Complex.exp_add]
  congr 1
  push_cast
  ring

private theorem constant_mul_phaseSignSums
    (c : Complex) (A B : PhaseSign → Complex) :
    c * (∑ leftSign ∈ phaseSignFinset, A leftSign) *
        (∑ rightSign ∈ phaseSignFinset, B rightSign) =
      ∑ leftSign ∈ phaseSignFinset,
        ∑ rightSign ∈ phaseSignFinset,
          c * A leftSign * B rightSign := by
  calc
    c * (∑ leftSign ∈ phaseSignFinset, A leftSign) *
        (∑ rightSign ∈ phaseSignFinset, B rightSign) =
      (∑ leftSign ∈ phaseSignFinset, c * A leftSign) *
        (∑ rightSign ∈ phaseSignFinset, B rightSign) := by
          apply congrArg
            (· * (∑ rightSign ∈ phaseSignFinset, B rightSign))
          exact Finset.mul_sum _ _ c
    _ = ∑ leftSign ∈ phaseSignFinset,
        (c * A leftSign) *
          (∑ rightSign ∈ phaseSignFinset, B rightSign) := by
          rw [Finset.sum_mul]
    _ = ∑ leftSign ∈ phaseSignFinset,
        ∑ rightSign ∈ phaseSignFinset,
          c * A leftSign * B rightSign := by
          apply Finset.sum_congr rfl
          intro leftSign _hleft
          rw [Finset.mul_sum]

/-- Pointwise expansion of the exact interaction-picture source into the
two-by-two signed input branches.  Each outer summand has the exact modular
relation `k = l + (k-l)`, and the deleted input modes have already vanished
by their bond symbols. -/
theorem interactionSource_eq_explicitBranchSum
    {N : Nat} [NeZero N] (alpha : Real)
    (outputSign : PhaseSign) (k : Site N)
    (p q : Time → HilbertConfiguration N)
    (tau : Real) :
    phaseFactor
        (phaseSignReal outputSign * equalMassFourierFrequency N k * tau) *
      complexFourierBranchSource (equalMassFourierFrequency N k) outputSign
        (nonzeroQuadraticForcing alpha k
          (fun l ↦ realFourierPosition l q) tau) =
      ∑ l ∈ nonzeroInputMomenta N k,
        ∑ leftSign ∈ phaseSignFinset,
          ∑ rightSign ∈ phaseSignFinset,
            equalMassQuadraticBranchTerm alpha k l
              outputSign leftSign rightSign p q tau := by
  have hcoordinate :
      (∑ l ∈ nonzeroInputMomenta N k,
          pureAlphaQuadraticFourierCoefficient N alpha k l *
            realFourierPosition l q tau *
            realFourierPosition (k - l) q tau) =
        ∑ l ∈ nonzeroInputMomenta N k,
          pureAlphaQuadraticFourierCoefficient N alpha k l *
            (∑ leftSign ∈ phaseSignFinset,
              equalMassBranchCoordinateTerm leftSign l p q tau) *
            (∑ rightSign ∈ phaseSignFinset,
              equalMassBranchCoordinateTerm rightSign (k - l) p q tau) := by
    apply Finset.sum_congr rfl
    intro l hl
    have hnonzero := mem_nonzeroInputMomenta.mp hl
    rw [realFourierPosition_eq_branch_sum l p q hnonzero.1 tau,
      realFourierPosition_eq_branch_sum (k - l) p q hnonzero.2 tau]
  unfold nonzeroQuadraticForcing
  rw [hcoordinate]
  unfold complexFourierBranchSource
  calc
    phaseFactor
          (phaseSignReal outputSign * equalMassFourierFrequency N k * tau) *
        ((phaseSignReal outputSign : Complex) * Complex.I *
          (∑ l ∈ nonzeroInputMomenta N k,
            pureAlphaQuadraticFourierCoefficient N alpha k l *
              (∑ leftSign ∈ phaseSignFinset,
                equalMassBranchCoordinateTerm leftSign l p q tau) *
              (∑ rightSign ∈ phaseSignFinset,
                equalMassBranchCoordinateTerm rightSign (k - l) p q tau)) /
          Real.sqrt (2 * equalMassFourierFrequency N k)) =
      ∑ l ∈ nonzeroInputMomenta N k,
        (phaseFactor
            (phaseSignReal outputSign * equalMassFourierFrequency N k * tau) *
          ((phaseSignReal outputSign : Complex) * Complex.I) /
          Real.sqrt (2 * equalMassFourierFrequency N k) *
          pureAlphaQuadraticFourierCoefficient N alpha k l) *
          (∑ leftSign ∈ phaseSignFinset,
            equalMassBranchCoordinateTerm leftSign l p q tau) *
          (∑ rightSign ∈ phaseSignFinset,
            equalMassBranchCoordinateTerm rightSign (k - l) p q tau) := by
        rw [show phaseFactor
              (phaseSignReal outputSign * equalMassFourierFrequency N k * tau) *
            ((phaseSignReal outputSign : Complex) * Complex.I *
              (∑ l ∈ nonzeroInputMomenta N k,
                pureAlphaQuadraticFourierCoefficient N alpha k l *
                  (∑ leftSign ∈ phaseSignFinset,
                    equalMassBranchCoordinateTerm leftSign l p q tau) *
                  (∑ rightSign ∈ phaseSignFinset,
                    equalMassBranchCoordinateTerm rightSign (k - l) p q tau)) /
              Real.sqrt (2 * equalMassFourierFrequency N k)) =
            (phaseFactor
                (phaseSignReal outputSign * equalMassFourierFrequency N k * tau) *
              ((phaseSignReal outputSign : Complex) * Complex.I) /
              Real.sqrt (2 * equalMassFourierFrequency N k)) *
              (∑ l ∈ nonzeroInputMomenta N k,
                pureAlphaQuadraticFourierCoefficient N alpha k l *
                  (∑ leftSign ∈ phaseSignFinset,
                    equalMassBranchCoordinateTerm leftSign l p q tau) *
                  (∑ rightSign ∈ phaseSignFinset,
                    equalMassBranchCoordinateTerm rightSign (k - l) p q tau)) by
              ring]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro l _hl
        ring
    _ = ∑ l ∈ nonzeroInputMomenta N k,
        ∑ leftSign ∈ phaseSignFinset,
          ∑ rightSign ∈ phaseSignFinset,
            (phaseFactor
                (phaseSignReal outputSign * equalMassFourierFrequency N k * tau) *
              ((phaseSignReal outputSign : Complex) * Complex.I) /
              Real.sqrt (2 * equalMassFourierFrequency N k) *
              pureAlphaQuadraticFourierCoefficient N alpha k l) *
              equalMassBranchCoordinateTerm leftSign l p q tau *
              equalMassBranchCoordinateTerm rightSign (k - l) p q tau := by
        apply Finset.sum_congr rfl
        intro l _hl
        exact constant_mul_phaseSignSums _ _ _
    _ = ∑ l ∈ nonzeroInputMomenta N k,
        ∑ leftSign ∈ phaseSignFinset,
          ∑ rightSign ∈ phaseSignFinset,
            equalMassQuadraticBranchTerm alpha k l
              outputSign leftSign rightSign p q tau := by
        apply Finset.sum_congr rfl
        intro l _hl
        apply Finset.sum_congr rfl
        intro leftSign _hleft
        apply Finset.sum_congr rfl
        intro rightSign _hright
        unfold equalMassBranchCoordinateTerm equalMassQuadraticBranchTerm
        rw [← phaseFactor_output_mul_inputs_eq_mismatch
          k l outputSign leftSign rightSign tau]
        unfold phaseRenormalize equalMassQuadraticBranchVertex
        ring

/-- Final exact interaction-picture equation for every nonzero output mode
of a differentiable pure-alpha Physlib trajectory. -/
theorem hasDerivAt_equalMassInteractionBranch_explicit
    {N : Nat} [NeZero N] (alpha : Real)
    (outputSign : PhaseSign) (k : Site N)
    (p q : Time → HilbertConfiguration N)
    (hHamilton :
      SatisfiesHamiltonEquations (unitMassConfig N) 1 0 alpha p q)
    (hp : Differentiable Real p) (hq : Differentiable Real q)
    (hk : k ≠ 0) (tau : Real) :
    HasDerivAt (equalMassInteractionBranch outputSign k p q)
      (∑ l ∈ nonzeroInputMomenta N k,
        ∑ leftSign ∈ phaseSignFinset,
          ∑ rightSign ∈ phaseSignFinset,
            equalMassQuadraticBranchTerm alpha k l
              outputSign leftSign rightSign p q tau) tau := by
  have hsource := hasDerivAt_equalMassInteractionBranch_source
    alpha outputSign k p q hHamilton hp hq hk tau
  exact hsource.congr_deriv
    (interactionSource_eq_explicitBranchSum
      alpha outputSign k p q tau)

end

end ArchonPhysics.EqualMassPeriodicFPUTInteractionPicture
