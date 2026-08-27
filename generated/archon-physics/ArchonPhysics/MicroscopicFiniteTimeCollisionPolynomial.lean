import ArchonPhysics.NormalizedModeCoupling
import ArchonPhysics.ResonanceWeightSinc
import Mathlib.RingTheory.MvPolynomial.Basic

/-!
# Microscopic finite-time three- and four-wave collision polynomials

This file packages an exact finite-dimensional algebraic object built from

* the normalized interaction vertex obtained after differentiating the
  Hamiltonian bond polynomial,
* the signed harmonic-frequency mismatch, and
* the squared finite-time oscillatory integral.

For fixed masses and observation time, the resulting object is literally an
`MvPolynomial` in the modal-action variables.  Its evaluation is a finite sum;
no kinetic limit, random-phase closure, positive-time assumption, or limiting
delta distribution is used.

The main structural statements are exact permutation and incoming/outgoing
sign-reversal symmetries.  The combined three-plus-four-wave polynomial also
reduces identically to its four-wave branch whenever the complete finite-time
three-wave kernel vanishes.  In particular this happens when the cubic
Hamiltonian coupling is zero.
-/

namespace ArchonPhysics.MicroscopicFiniteTimeCollisionPolynomial

open ArchonPhysics
open FiniteTimeResonanceWeight
open ModalPhaseMismatch
open ModeCoupling
open NormalizedModeCoupling
open ResonanceWeightSinc

noncomputable section

/-- Ordered mode tuples of one finite interaction. -/
abbrev ModeTuple (N n : Nat) := Fin n → Lattice.Site N

/-- Permuting the interaction legs is an equivalence of the finite tuple
space. -/
def permuteModeTuple {N n : Nat} (sigma : Equiv.Perm (Fin n)) :
    ModeTuple N n ≃ ModeTuple N n where
  toFun modes := modes ∘ sigma
  invFun modes := modes ∘ sigma.symm
  left_inv modes := by
    funext r
    simp [Function.comp_apply]
  right_inv modes := by
    funext r
    simp [Function.comp_apply]

/-- The physical interaction vertex, including the force-level coefficient
obtained after differentiating the corresponding bond-potential monomial.
For example, `alpha / 3 * x^3` in the Hamiltonian contributes the coupling
`alpha` here. -/
def hamiltonianInteractionVertex {N n : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (coupling : Real)
    (modes : ModeTuple N n) : Real :=
  coupling * normalizedInteractionVertex m modes

/-- Exact finite-time second-order collision coefficient for one ordered mode
tuple.  It is a squared Hamiltonian vertex times the finite-time mismatch
weight. -/
def finiteTimeCollisionKernel {N n : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (coupling : Real)
    (sign : Fin n → InteractionSign) (T : Real)
    (modes : ModeTuple N n) : Real :=
  (hamiltonianInteractionVertex m coupling modes) ^ 2 *
    finiteTimeResonanceWeight (phaseMismatch m sign modes) T

/-- The action monomial associated with one ordered mode tuple. -/
def collisionActionMonomial {N n : Nat} (modes : ModeTuple N n) :
    MvPolynomial (Lattice.Site N) Real :=
  ∏ r, MvPolynomial.X (modes r)

/-- The exact microscopic finite-time collision polynomial.  Its coefficients
are fixed by the Hamiltonian vertex, mismatch, and observation time; its
variables are modal actions. -/
def microscopicFiniteTimeCollisionPolynomial {N n : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (coupling : Real)
    (sign : Fin n → InteractionSign) (T : Real) :
    MvPolynomial (Lattice.Site N) Real :=
  ∑ modes : ModeTuple N n,
    MvPolynomial.C (finiteTimeCollisionKernel m coupling sign T modes) *
      collisionActionMonomial modes

/-- Direct finite-sum evaluation of the microscopic polynomial on a modal
action profile. -/
def microscopicFiniteTimeCollisionFunctional {N n : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (coupling : Real)
    (sign : Fin n → InteractionSign) (T : Real)
    (action : Lattice.Site N → Real) : Real :=
  ∑ modes : ModeTuple N n,
    finiteTimeCollisionKernel m coupling sign T modes *
      ∏ r, action (modes r)

/-- Evaluating the literal multivariate polynomial is the displayed finite
collision sum. -/
theorem eval_microscopicFiniteTimeCollisionPolynomial {N n : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (coupling : Real)
    (sign : Fin n → InteractionSign) (T : Real)
    (action : Lattice.Site N → Real) :
    MvPolynomial.eval action
        (microscopicFiniteTimeCollisionPolynomial m coupling sign T) =
      microscopicFiniteTimeCollisionFunctional m coupling sign T action := by
  simp [microscopicFiniteTimeCollisionPolynomial,
    microscopicFiniteTimeCollisionFunctional, collisionActionMonomial]

/-- Every tuplewise finite-time collision coefficient is nonnegative, with no
assumption on the sign of `T`. -/
theorem finiteTimeCollisionKernel_nonneg {N n : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (coupling : Real)
    (sign : Fin n → InteractionSign) (T : Real)
    (modes : ModeTuple N n) :
    0 ≤ finiteTimeCollisionKernel m coupling sign T modes := by
  exact mul_nonneg (sq_nonneg _)
    (finiteTimeResonanceWeight_nonneg _ _)

/-- Evaluation on nonnegative modal actions is nonnegative. -/
theorem microscopicFiniteTimeCollisionFunctional_nonneg
    {N n : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (coupling : Real)
    (sign : Fin n → InteractionSign) (T : Real)
    (action : Lattice.Site N → Real)
    (haction : ∀ k, 0 ≤ action k) :
    0 ≤ microscopicFiniteTimeCollisionFunctional
      m coupling sign T action := by
  unfold microscopicFiniteTimeCollisionFunctional
  apply Finset.sum_nonneg
  intro modes _hmodes
  apply mul_nonneg (finiteTimeCollisionKernel_nonneg m coupling sign T modes)
  exact Finset.prod_nonneg fun r _hr ↦ haction (modes r)

/-- With the total convention for finite-time weights, nonpositive observation
times give the zero tuple kernel. -/
theorem finiteTimeCollisionKernel_eq_zero_of_nonpos
    {N n : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (coupling : Real)
    (sign : Fin n → InteractionSign) {T : Real} (hT : T ≤ 0)
    (modes : ModeTuple N n) :
    finiteTimeCollisionKernel m coupling sign T modes = 0 := by
  simp [finiteTimeCollisionKernel,
    finiteTimeResonanceWeight_of_nonpos hT]

/-- Consequently the complete microscopic polynomial is zero at every
nonpositive observation time. -/
theorem microscopicFiniteTimeCollisionPolynomial_eq_zero_of_nonpos
    {N n : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (coupling : Real)
    (sign : Fin n → InteractionSign) {T : Real} (hT : T ≤ 0) :
    microscopicFiniteTimeCollisionPolynomial m coupling sign T = 0 := by
  unfold microscopicFiniteTimeCollisionPolynomial
  apply Finset.sum_eq_zero
  intro modes _hmodes
  rw [finiteTimeCollisionKernel_eq_zero_of_nonpos m coupling sign hT modes]
  simp

/-- Simultaneous permutation of signs and modes leaves the signed mismatch
unchanged. -/
theorem phaseMismatch_perm {N n : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N)
    (sign : Fin n → InteractionSign) (modes : ModeTuple N n)
    (sigma : Equiv.Perm (Fin n)) :
    phaseMismatch m (sign ∘ sigma) (modes ∘ sigma) =
      phaseMismatch m sign modes := by
  unfold phaseMismatch
  simpa [Function.comp_apply] using
    (Equiv.sum_comp sigma
      (fun r ↦ (sign r).coefficient * modeFrequency m (modes r)))

/-- The Hamiltonian vertex is symmetric in all interaction legs. -/
theorem hamiltonianInteractionVertex_perm {N n : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (coupling : Real)
    (modes : ModeTuple N n) (sigma : Equiv.Perm (Fin n)) :
    hamiltonianInteractionVertex m coupling (modes ∘ sigma) =
      hamiltonianInteractionVertex m coupling modes := by
  unfold hamiltonianInteractionVertex
  rw [normalizedInteractionVertex_perm]

/-- The complete tuple kernel is invariant under a simultaneous leg
permutation. -/
theorem finiteTimeCollisionKernel_perm {N n : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (coupling : Real)
    (sign : Fin n → InteractionSign) (T : Real)
    (modes : ModeTuple N n) (sigma : Equiv.Perm (Fin n)) :
    finiteTimeCollisionKernel m coupling (sign ∘ sigma) T
        (modes ∘ sigma) =
      finiteTimeCollisionKernel m coupling sign T modes := by
  unfold finiteTimeCollisionKernel
  rw [hamiltonianInteractionVertex_perm, phaseMismatch_perm]

/-- The action monomial is symmetric in its ordered legs. -/
theorem collisionActionMonomial_perm {N n : Nat}
    (modes : ModeTuple N n) (sigma : Equiv.Perm (Fin n)) :
    collisionActionMonomial (modes ∘ sigma) =
      collisionActionMonomial modes := by
  unfold collisionActionMonomial
  simpa [Function.comp_apply] using
    (Equiv.prod_comp sigma
      (fun r ↦ (MvPolynomial.X (modes r) :
        MvPolynomial (Lattice.Site N) Real)))

/-- The whole microscopic polynomial is independent of the arbitrary ordering
of its interaction legs. -/
theorem microscopicFiniteTimeCollisionPolynomial_perm
    {N n : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (coupling : Real)
    (sign : Fin n → InteractionSign) (T : Real)
    (sigma : Equiv.Perm (Fin n)) :
    microscopicFiniteTimeCollisionPolynomial
        m coupling (sign ∘ sigma) T =
      microscopicFiniteTimeCollisionPolynomial m coupling sign T := by
  classical
  unfold microscopicFiniteTimeCollisionPolynomial
  let summand : ModeTuple N n → MvPolynomial (Lattice.Site N) Real :=
    fun modes ↦
      MvPolynomial.C
          (finiteTimeCollisionKernel m coupling (sign ∘ sigma) T modes) *
        collisionActionMonomial modes
  calc
    (∑ modes : ModeTuple N n,
        MvPolynomial.C
            (finiteTimeCollisionKernel m coupling (sign ∘ sigma) T modes) *
          collisionActionMonomial modes) =
        ∑ modes : ModeTuple N n, summand ((permuteModeTuple sigma) modes) := by
      exact (Equiv.sum_comp (permuteModeTuple sigma) summand).symm
    _ = ∑ modes : ModeTuple N n,
        MvPolynomial.C (finiteTimeCollisionKernel m coupling sign T modes) *
          collisionActionMonomial modes := by
      apply Finset.sum_congr rfl
      intro modes _hmodes
      dsimp [summand, permuteModeTuple]
      rw [finiteTimeCollisionKernel_perm, collisionActionMonomial_perm]

/-- Opposite interaction sign. -/
def oppositeSign : InteractionSign → InteractionSign
  | .plus => .minus
  | .minus => .plus

@[simp] theorem oppositeSign_coefficient (s : InteractionSign) :
    (oppositeSign s).coefficient = -s.coefficient := by
  cases s <;> norm_num [oppositeSign, InteractionSign.coefficient]

/-- Reverse every incoming/outgoing sign in a pattern. -/
def reverseSignPattern {n : Nat}
    (sign : Fin n → InteractionSign) : Fin n → InteractionSign :=
  fun r ↦ oppositeSign (sign r)

/-- Reversing all interaction signs negates the mismatch exactly. -/
theorem phaseMismatch_reverseSignPattern {N n : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N)
    (sign : Fin n → InteractionSign) (modes : ModeTuple N n) :
    phaseMismatch m (reverseSignPattern sign) modes =
      -phaseMismatch m sign modes := by
  unfold phaseMismatch reverseSignPattern
  simp_rw [oppositeSign_coefficient, neg_mul]
  rw [Finset.sum_neg_distrib]

/-- Squaring the oscillatory integral makes the finite-time kernel invariant
under global incoming/outgoing reversal. -/
theorem finiteTimeCollisionKernel_reverseSignPattern
    {N n : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (coupling : Real)
    (sign : Fin n → InteractionSign) (T : Real)
    (modes : ModeTuple N n) :
    finiteTimeCollisionKernel m coupling (reverseSignPattern sign) T modes =
      finiteTimeCollisionKernel m coupling sign T modes := by
  unfold finiteTimeCollisionKernel
  rw [phaseMismatch_reverseSignPattern,
    finiteTimeResonanceWeight_neg]

/-- The complete collision polynomial has the same global sign-reversal
symmetry. -/
theorem microscopicFiniteTimeCollisionPolynomial_reverseSignPattern
    {N n : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (coupling : Real)
    (sign : Fin n → InteractionSign) (T : Real) :
    microscopicFiniteTimeCollisionPolynomial
        m coupling (reverseSignPattern sign) T =
      microscopicFiniteTimeCollisionPolynomial m coupling sign T := by
  unfold microscopicFiniteTimeCollisionPolynomial
  apply Finset.sum_congr rfl
  intro modes _hmodes
  rw [finiteTimeCollisionKernel_reverseSignPattern]

/-- Literal three-wave specialization. -/
def threeWaveCollisionPolynomial {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (cubicCoupling : Real)
    (sign : Fin 3 → InteractionSign) (T : Real) :
    MvPolynomial (Lattice.Site N) Real :=
  microscopicFiniteTimeCollisionPolynomial m cubicCoupling sign T

/-- Literal four-wave specialization. -/
def fourWaveCollisionPolynomial {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (quarticCoupling : Real)
    (sign : Fin 4 → InteractionSign) (T : Real) :
    MvPolynomial (Lattice.Site N) Real :=
  microscopicFiniteTimeCollisionPolynomial m quarticCoupling sign T

/-- The microscopic polynomial retaining both the cubic and quartic
Hamiltonian branches. -/
def threeFourCollisionPolynomial {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N)
    (cubicCoupling quarticCoupling : Real)
    (signThree : Fin 3 → InteractionSign)
    (signFour : Fin 4 → InteractionSign) (T : Real) :
    MvPolynomial (Lattice.Site N) Real :=
  threeWaveCollisionPolynomial m cubicCoupling signThree T +
    fourWaveCollisionPolynomial m quarticCoupling signFour T

/-- Exact predicate saying that the complete finite-time tuple kernel
vanishes, not merely that there are no exact resonances. -/
def CollisionKernelVanishes {N n : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (coupling : Real)
    (sign : Fin n → InteractionSign) (T : Real) : Prop :=
  ∀ modes : ModeTuple N n,
    finiteTimeCollisionKernel m coupling sign T modes = 0

/-- A vanishing tuple kernel gives the zero microscopic polynomial. -/
theorem microscopicFiniteTimeCollisionPolynomial_eq_zero_of_kernelVanishes
    {N n : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (coupling : Real)
    (sign : Fin n → InteractionSign) (T : Real)
    (hkernel : CollisionKernelVanishes m coupling sign T) :
    microscopicFiniteTimeCollisionPolynomial m coupling sign T = 0 := by
  unfold microscopicFiniteTimeCollisionPolynomial
  apply Finset.sum_eq_zero
  intro modes _hmodes
  rw [hkernel modes]
  simp

/-- A zero force-level interaction coupling makes the complete finite-time
kernel vanish. -/
theorem collisionKernelVanishes_of_coupling_eq_zero
    {N n : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) {coupling : Real}
    (sign : Fin n → InteractionSign) (T : Real)
    (hcoupling : coupling = 0) :
    CollisionKernelVanishes m coupling sign T := by
  intro modes
  simp [finiteTimeCollisionKernel, hamiltonianInteractionVertex, hcoupling]

/-- Vanishing normalized Hamiltonian vertices also make the finite-time kernel
vanish, independently of the mismatch and observation time. -/
theorem collisionKernelVanishes_of_normalizedVertex_eq_zero
    {N n : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (coupling : Real)
    (sign : Fin n → InteractionSign) (T : Real)
    (hvertex : ∀ modes : ModeTuple N n,
      normalizedInteractionVertex m modes = 0) :
    CollisionKernelVanishes m coupling sign T := by
  intro modes
  simp [finiteTimeCollisionKernel, hamiltonianInteractionVertex,
    hvertex modes]

/-- Exact automatic branch selection: when the complete finite-time
three-wave kernel vanishes, the retained three-plus-four-wave polynomial is
identically its four-wave branch. -/
theorem threeFourCollisionPolynomial_eq_four_of_threeKernelVanishes
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N)
    (cubicCoupling quarticCoupling : Real)
    (signThree : Fin 3 → InteractionSign)
    (signFour : Fin 4 → InteractionSign) (T : Real)
    (hthree : CollisionKernelVanishes m cubicCoupling signThree T) :
    threeFourCollisionPolynomial m cubicCoupling quarticCoupling
        signThree signFour T =
      fourWaveCollisionPolynomial m quarticCoupling signFour T := by
  unfold threeFourCollisionPolynomial threeWaveCollisionPolynomial
  rw [microscopicFiniteTimeCollisionPolynomial_eq_zero_of_kernelVanishes
    m cubicCoupling signThree T hthree]
  exact zero_add _

/-- FPUT `alpha-beta` convention.  Although the Hamiltonian coefficients of
the cubic and quartic bond powers are `alpha / 3` and `beta / 4`, the
corresponding force/vertex coefficients are `alpha` and `beta`; those are the
couplings consumed by `finiteTimeCollisionKernel`. -/
def fputAlphaBetaCollisionPolynomial {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (alpha beta : Real)
    (signThree : Fin 3 → InteractionSign)
    (signFour : Fin 4 → InteractionSign) (T : Real) :
    MvPolynomial (Lattice.Site N) Real :=
  threeFourCollisionPolynomial m alpha beta
    signThree signFour T

/-- For a reflection-symmetric FPUT potential (`alpha = 0`), the exact
finite-time polynomial automatically reduces to the four-wave branch. -/
theorem fputAlphaBetaCollisionPolynomial_eq_four_of_alpha_eq_zero
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) {alpha beta : Real}
    (signThree : Fin 3 → InteractionSign)
    (signFour : Fin 4 → InteractionSign) (T : Real)
    (halpha : alpha = 0) :
    fputAlphaBetaCollisionPolynomial m alpha beta signThree signFour T =
      fourWaveCollisionPolynomial m beta signFour T := by
  unfold fputAlphaBetaCollisionPolynomial
  apply threeFourCollisionPolynomial_eq_four_of_threeKernelVanishes
  exact collisionKernelVanishes_of_coupling_eq_zero
    m signThree T halpha

end

end ArchonPhysics.MicroscopicFiniteTimeCollisionPolynomial
