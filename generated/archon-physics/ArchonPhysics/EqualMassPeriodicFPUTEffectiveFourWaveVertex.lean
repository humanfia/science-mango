import ArchonPhysics.EqualMassPeriodicFPUTFourierHamiltonian
import ArchonPhysics.EqualMassPeriodicFPUTFourierThreeWave

/-!
# Equal-mass periodic alpha-FPUT: the finite effective four-wave vertex

This module indexes the two quadratic Fourier vertices which occur at second
Picard order.  A diagram records the outer insertion slot, four real-phase
branches, one intermediate momentum, and the four external momenta.  The
inner nonresonant divisor is eliminated by the existing finite nested
normal-form identity.

The resulting statements are exact finite-`N` algebra.  They identify the
four-leg momentum and frequency mismatch, the two powers of `alpha`, and the
zero-mode selection rule.  They do not assert positivity, a kinetic limit,
near-resonance counting, or any bound uniform in `N`.
-/

namespace ArchonPhysics.EqualMassPeriodicFPUTEffectiveFourWaveVertex

open scoped BigOperators ComplexConjugate

open ArchonPhysics
open ArchonPhysics.EqualMassPeriodicFPUTFourierHamiltonian
open ArchonPhysics.EqualMassPeriodicFPUTFourierThreeWave
open ArchonPhysics.FiniteNestedNormalFormExtraction
open ArchonPhysics.FinitePhaseMonomials
open ArchonPhysics.FreeFPUTCollisionMismatchBridge
open ArchonPhysics.FreeFPUTTensorPhaseExpansion
open ArchonPhysics.Lattice
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.NonresonantOscillatoryGain
open ArchonPhysics.PhyslibFPUTBinaryInteractionTreeCouples

noncomputable section

/-! ## Explicit two-vertex diagram data -/

/-- A finite two-vertex diagram index.

* the `Fin 2` component is the outer insertion slot (`0` for left);
* `Fin 4 → Fin 2` stores inserted, spectator, inner-left, inner-right
  phase/conjugate branches in that order;
* `Fin 5 → Site N` stores output, intermediate, spectator, inner-left,
  inner-right momenta in that order.
-/
abbrev EffectiveFourWaveDiagram (N : Nat) :=
  Fin 2 × ((Fin 4 → Fin 2) × (Fin 5 → Site N))

def outerInsertionSlot {N : Nat} (diagram : EffectiveFourWaveDiagram N) : Fin 2 :=
  diagram.1

def diagramBranch {N : Nat} (diagram : EffectiveFourWaveDiagram N)
    (slot : Fin 4) : PhaseSign :=
  binaryPhaseSign (diagram.2.1 slot)

def insertedBranch {N : Nat} (diagram : EffectiveFourWaveDiagram N) : PhaseSign :=
  diagramBranch diagram 0

def spectatorBranch {N : Nat} (diagram : EffectiveFourWaveDiagram N) : PhaseSign :=
  diagramBranch diagram 1

def innerLeftBranch {N : Nat} (diagram : EffectiveFourWaveDiagram N) : PhaseSign :=
  diagramBranch diagram 2

def innerRightBranch {N : Nat} (diagram : EffectiveFourWaveDiagram N) : PhaseSign :=
  diagramBranch diagram 3

def diagramMode {N : Nat} (diagram : EffectiveFourWaveDiagram N)
    (slot : Fin 5) : Site N :=
  diagram.2.2 slot

def outputMomentum {N : Nat} (diagram : EffectiveFourWaveDiagram N) : Site N :=
  diagramMode diagram 0

def intermediateMomentum {N : Nat} (diagram : EffectiveFourWaveDiagram N) : Site N :=
  diagramMode diagram 1

def spectatorMomentum {N : Nat} (diagram : EffectiveFourWaveDiagram N) : Site N :=
  diagramMode diagram 2

def innerLeftMomentum {N : Nat} (diagram : EffectiveFourWaveDiagram N) : Site N :=
  diagramMode diagram 3

def innerRightMomentum {N : Nat} (diagram : EffectiveFourWaveDiagram N) : Site N :=
  diagramMode diagram 4

/-- Phase/conjugate action on an underlying Fourier label. -/
def phaseSignedMomentum {N : Nat} : PhaseSign → Site N → Site N
  | .phase, momentum => momentum
  | .conjugate, momentum => -momentum

@[simp] theorem phaseSignedMomentum_zero
    {N : Nat} (sign : PhaseSign) :
    phaseSignedMomentum sign (0 : Site N) = 0 := by
  cases sign <;> simp [phaseSignedMomentum]

theorem phaseSignedMomentum_add
    {N : Nat} (sign : PhaseSign) (left right : Site N) :
    phaseSignedMomentum sign (left + right) =
      phaseSignedMomentum sign left + phaseSignedMomentum sign right := by
  cases sign
  · rfl
  · simp only [phaseSignedMomentum]
    abel

theorem phaseSignedMomentum_compose
    {N : Nat} (outer inner : PhaseSign) (momentum : Site N) :
    phaseSignedMomentum (composePhaseSign outer inner) momentum =
      phaseSignedMomentum outer (phaseSignedMomentum inner momentum) := by
  cases outer <;> cases inner <;>
    simp [composePhaseSign, phaseSignedMomentum]

theorem interactionSignMomentum_inputBranch
    {N : Nat} (sign : PhaseSign) (momentum : Site N) :
    interactionSignMomentum (phaseSignToInputInteractionSign sign) momentum =
      -phaseSignedMomentum sign momentum := by
  cases sign <;>
    simp [phaseSignToInputInteractionSign, interactionSignMomentum,
      phaseSignedMomentum]

@[simp] theorem interactionSignMomentum_plus_local
    {N : Nat} (momentum : Site N) :
    interactionSignMomentum .plus momentum = momentum := rfl

/-- The two literal convolution constraints, before the intermediate mode is
eliminated. -/
def IsTwoVertexMomentumSupported
    {N : Nat} (diagram : EffectiveFourWaveDiagram N) : Prop :=
  outputMomentum diagram =
      phaseSignedMomentum (insertedBranch diagram)
          (intermediateMomentum diagram) +
        phaseSignedMomentum (spectatorBranch diagram)
          (spectatorMomentum diagram) ∧
    intermediateMomentum diagram =
      phaseSignedMomentum (innerLeftBranch diagram)
          (innerLeftMomentum diagram) +
        phaseSignedMomentum (innerRightBranch diagram)
          (innerRightMomentum diagram)

/-! ## Three-leg inner divisor and four-leg external data -/

def innerSignedFourierTriple
    {N : Nat} (diagram : EffectiveFourWaveDiagram N) : SignedFourierTriple N :=
  (Fin.cons .plus
      (Fin.cons (phaseSignToInputInteractionSign (innerLeftBranch diagram))
        (fun _ ↦ phaseSignToInputInteractionSign (innerRightBranch diagram))),
    Fin.cons (intermediateMomentum diagram)
      (Fin.cons (innerLeftMomentum diagram) (fun _ ↦ innerRightMomentum diagram)))

def outerSignedFourierTriple
    {N : Nat} (diagram : EffectiveFourWaveDiagram N) : SignedFourierTriple N :=
  (Fin.cons .plus
      (Fin.cons (phaseSignToInputInteractionSign (insertedBranch diagram))
        (fun _ ↦ phaseSignToInputInteractionSign (spectatorBranch diagram))),
    Fin.cons (outputMomentum diagram)
      (Fin.cons (intermediateMomentum diagram) (fun _ ↦ spectatorMomentum diagram)))

@[simp] theorem innerSignedFourierTriple_sign_zero
    {N : Nat} (diagram : EffectiveFourWaveDiagram N) :
    (innerSignedFourierTriple diagram).1 0 = .plus := rfl

@[simp] theorem innerSignedFourierTriple_sign_one
    {N : Nat} (diagram : EffectiveFourWaveDiagram N) :
    (innerSignedFourierTriple diagram).1 1 =
      phaseSignToInputInteractionSign (innerLeftBranch diagram) := rfl

@[simp] theorem innerSignedFourierTriple_sign_two
    {N : Nat} (diagram : EffectiveFourWaveDiagram N) :
    (innerSignedFourierTriple diagram).1 2 =
      phaseSignToInputInteractionSign (innerRightBranch diagram) := rfl

@[simp] theorem innerSignedFourierTriple_mode_zero
    {N : Nat} (diagram : EffectiveFourWaveDiagram N) :
    (innerSignedFourierTriple diagram).2 0 = intermediateMomentum diagram := rfl

@[simp] theorem innerSignedFourierTriple_mode_one
    {N : Nat} (diagram : EffectiveFourWaveDiagram N) :
    (innerSignedFourierTriple diagram).2 1 = innerLeftMomentum diagram := rfl

@[simp] theorem innerSignedFourierTriple_mode_two
    {N : Nat} (diagram : EffectiveFourWaveDiagram N) :
    (innerSignedFourierTriple diagram).2 2 = innerRightMomentum diagram := rfl

@[simp] theorem outerSignedFourierTriple_sign_zero
    {N : Nat} (diagram : EffectiveFourWaveDiagram N) :
    (outerSignedFourierTriple diagram).1 0 = .plus := rfl

@[simp] theorem outerSignedFourierTriple_sign_one
    {N : Nat} (diagram : EffectiveFourWaveDiagram N) :
    (outerSignedFourierTriple diagram).1 1 =
      phaseSignToInputInteractionSign (insertedBranch diagram) := rfl

@[simp] theorem outerSignedFourierTriple_sign_two
    {N : Nat} (diagram : EffectiveFourWaveDiagram N) :
    (outerSignedFourierTriple diagram).1 2 =
      phaseSignToInputInteractionSign (spectatorBranch diagram) := rfl

@[simp] theorem outerSignedFourierTriple_mode_zero
    {N : Nat} (diagram : EffectiveFourWaveDiagram N) :
    (outerSignedFourierTriple diagram).2 0 = outputMomentum diagram := rfl

@[simp] theorem outerSignedFourierTriple_mode_one
    {N : Nat} (diagram : EffectiveFourWaveDiagram N) :
    (outerSignedFourierTriple diagram).2 1 = intermediateMomentum diagram := rfl

@[simp] theorem outerSignedFourierTriple_mode_two
    {N : Nat} (diagram : EffectiveFourWaveDiagram N) :
    (outerSignedFourierTriple diagram).2 2 = spectatorMomentum diagram := rfl

/-- Raw mismatch of the inner quadratic source. -/
def innerThreeWaveMismatch
    {N : Nat} [NeZero N] (diagram : EffectiveFourWaveDiagram N) : Real :=
  signedFourierTripleMismatch (innerSignedFourierTriple diagram)

/-- Mismatch of the outer quadratic source before inserting the inner
evolution. -/
def outerThreeWaveMismatch
    {N : Nat} [NeZero N] (diagram : EffectiveFourWaveDiagram N) : Real :=
  signedFourierTripleMismatch (outerSignedFourierTriple diagram)

/-- Homological divisor carried by the inserted branch.  Conjugating the
inserted amplitude reverses the inner phase. -/
def innerHomologicalDivisor
    {N : Nat} [NeZero N] (diagram : EffectiveFourWaveDiagram N) : Real :=
  phaseSignActReal (insertedBranch diagram) (innerThreeWaveMismatch diagram)

/-- External four-wave signs: output, spectator, and the two inner leaves.
The outer inserted branch composes with both inner branches. -/
def totalFourWaveSign
    {N : Nat} (diagram : EffectiveFourWaveDiagram N) : Fin 4 → InteractionSign :=
  Fin.cons .plus
    (Fin.cons (phaseSignToInputInteractionSign (spectatorBranch diagram))
      (Fin.cons
        (phaseSignToInputInteractionSign
          (composePhaseSign (insertedBranch diagram) (innerLeftBranch diagram)))
        (fun _ ↦ phaseSignToInputInteractionSign
          (composePhaseSign (insertedBranch diagram) (innerRightBranch diagram)))))

def totalFourWaveModes
    {N : Nat} (diagram : EffectiveFourWaveDiagram N) : Fin 4 → Site N :=
  Fin.cons (outputMomentum diagram)
    (Fin.cons (spectatorMomentum diagram)
      (Fin.cons (innerLeftMomentum diagram) (fun _ ↦ innerRightMomentum diagram)))

@[simp] theorem totalFourWaveSign_zero
    {N : Nat} (diagram : EffectiveFourWaveDiagram N) :
    totalFourWaveSign diagram 0 = .plus := rfl

@[simp] theorem totalFourWaveSign_one
    {N : Nat} (diagram : EffectiveFourWaveDiagram N) :
    totalFourWaveSign diagram 1 =
      phaseSignToInputInteractionSign (spectatorBranch diagram) := rfl

@[simp] theorem totalFourWaveSign_two
    {N : Nat} (diagram : EffectiveFourWaveDiagram N) :
    totalFourWaveSign diagram 2 =
      phaseSignToInputInteractionSign
        (composePhaseSign (insertedBranch diagram) (innerLeftBranch diagram)) := rfl

@[simp] theorem totalFourWaveSign_three
    {N : Nat} (diagram : EffectiveFourWaveDiagram N) :
    totalFourWaveSign diagram 3 =
      phaseSignToInputInteractionSign
        (composePhaseSign (insertedBranch diagram) (innerRightBranch diagram)) := rfl

@[simp] theorem totalFourWaveModes_zero
    {N : Nat} (diagram : EffectiveFourWaveDiagram N) :
    totalFourWaveModes diagram 0 = outputMomentum diagram := rfl

@[simp] theorem totalFourWaveModes_one
    {N : Nat} (diagram : EffectiveFourWaveDiagram N) :
    totalFourWaveModes diagram 1 = spectatorMomentum diagram := rfl

@[simp] theorem totalFourWaveModes_two
    {N : Nat} (diagram : EffectiveFourWaveDiagram N) :
    totalFourWaveModes diagram 2 = innerLeftMomentum diagram := rfl

@[simp] theorem totalFourWaveModes_three
    {N : Nat} (diagram : EffectiveFourWaveDiagram N) :
    totalFourWaveModes diagram 3 = innerRightMomentum diagram := rfl

def totalFourWaveMomentum
    {N : Nat} (diagram : EffectiveFourWaveDiagram N) : Site N :=
  signedFourierMomentum (totalFourWaveSign diagram) (totalFourWaveModes diagram)

def totalFourWaveMismatch
    {N : Nat} [NeZero N] (diagram : EffectiveFourWaveDiagram N) : Real :=
  periodicSinePhaseMismatch (totalFourWaveSign diagram) (totalFourWaveModes diagram)

theorem signedFourierMomentum_innerSignedFourierTriple
    {N : Nat} (diagram : EffectiveFourWaveDiagram N) :
    signedFourierMomentum (innerSignedFourierTriple diagram).1
        (innerSignedFourierTriple diagram).2 =
      intermediateMomentum diagram -
        phaseSignedMomentum (innerLeftBranch diagram) (innerLeftMomentum diagram) -
        phaseSignedMomentum (innerRightBranch diagram) (innerRightMomentum diagram) := by
  unfold signedFourierMomentum
  simp [Fin.sum_univ_three, interactionSignMomentum_inputBranch]
  abel

theorem totalFourWaveMomentum_eq_explicit
    {N : Nat} (diagram : EffectiveFourWaveDiagram N) :
    totalFourWaveMomentum diagram =
      outputMomentum diagram -
        phaseSignedMomentum (spectatorBranch diagram) (spectatorMomentum diagram) -
        phaseSignedMomentum
          (composePhaseSign (insertedBranch diagram) (innerLeftBranch diagram))
          (innerLeftMomentum diagram) -
        phaseSignedMomentum
          (composePhaseSign (insertedBranch diagram) (innerRightBranch diagram))
          (innerRightMomentum diagram) := by
  unfold totalFourWaveMomentum signedFourierMomentum
  simp [Fin.sum_univ_four, interactionSignMomentum_inputBranch]
  abel

theorem innerThreeWaveMismatch_eq_explicit
    {N : Nat} [NeZero N] (diagram : EffectiveFourWaveDiagram N) :
    innerThreeWaveMismatch diagram =
      periodicSineFrequency N (intermediateMomentum diagram) -
        ((innerLeftBranch diagram).exponent : Real) *
          periodicSineFrequency N (innerLeftMomentum diagram) -
        ((innerRightBranch diagram).exponent : Real) *
          periodicSineFrequency N (innerRightMomentum diagram) := by
  unfold innerThreeWaveMismatch signedFourierTripleMismatch
    periodicSinePhaseMismatch
  simp [Fin.sum_univ_three, coefficient_phaseSignToInputInteractionSign]
  ring

theorem outerThreeWaveMismatch_eq_explicit
    {N : Nat} [NeZero N] (diagram : EffectiveFourWaveDiagram N) :
    outerThreeWaveMismatch diagram =
      periodicSineFrequency N (outputMomentum diagram) -
        ((insertedBranch diagram).exponent : Real) *
          periodicSineFrequency N (intermediateMomentum diagram) -
        ((spectatorBranch diagram).exponent : Real) *
          periodicSineFrequency N (spectatorMomentum diagram) := by
  unfold outerThreeWaveMismatch signedFourierTripleMismatch
    periodicSinePhaseMismatch
  simp [Fin.sum_univ_three, coefficient_phaseSignToInputInteractionSign]
  ring

theorem totalFourWaveMismatch_eq_explicit
    {N : Nat} [NeZero N] (diagram : EffectiveFourWaveDiagram N) :
    totalFourWaveMismatch diagram =
      periodicSineFrequency N (outputMomentum diagram) -
        ((spectatorBranch diagram).exponent : Real) *
          periodicSineFrequency N (spectatorMomentum diagram) -
        ((composePhaseSign (insertedBranch diagram)
            (innerLeftBranch diagram)).exponent : Real) *
          periodicSineFrequency N (innerLeftMomentum diagram) -
        ((composePhaseSign (insertedBranch diagram)
            (innerRightBranch diagram)).exponent : Real) *
          periodicSineFrequency N (innerRightMomentum diagram) := by
  unfold totalFourWaveMismatch periodicSinePhaseMismatch
  simp [Fin.sum_univ_four, coefficient_phaseSignToInputInteractionSign]
  ring

theorem innerTriple_momentumBalanced_of_supported
    {N : Nat} (diagram : EffectiveFourWaveDiagram N)
    (hsupported : IsTwoVertexMomentumSupported diagram) :
    FourierMomentumBalanced (innerSignedFourierTriple diagram).1
      (innerSignedFourierTriple diagram).2 := by
  unfold FourierMomentumBalanced
  rw [signedFourierMomentum_innerSignedFourierTriple]
  rw [hsupported.2]
  abel

theorem totalFourWaveMomentum_eq_zero_of_supported
    {N : Nat} (diagram : EffectiveFourWaveDiagram N)
    (hsupported : IsTwoVertexMomentumSupported diagram) :
    totalFourWaveMomentum diagram = 0 := by
  rw [totalFourWaveMomentum_eq_explicit, hsupported.1, hsupported.2,
    phaseSignedMomentum_add,
    ← phaseSignedMomentum_compose,
    ← phaseSignedMomentum_compose]
  abel

/-- The intermediate frequency cancels exactly: outer plus signed inner
mismatch is the literal signed four-wave mismatch. -/
theorem outer_add_innerHomologicalDivisor_eq_totalFourWaveMismatch
    {N : Nat} [NeZero N] (diagram : EffectiveFourWaveDiagram N) :
    outerThreeWaveMismatch diagram + innerHomologicalDivisor diagram =
      totalFourWaveMismatch diagram := by
  rw [outerThreeWaveMismatch_eq_explicit,
    totalFourWaveMismatch_eq_explicit]
  unfold innerHomologicalDivisor phaseSignActReal
  rw [innerThreeWaveMismatch_eq_explicit]
  simp only [PhaseSign.exponent_compose]
  push_cast
  ring

/-! ## Active inner shell and its fixed-volume divisor gap -/

/-- Active diagrams have both exact vertex momentum selectors and no zero
mode among output, intermediate, spectator, or either inner leaf. -/
def IsActiveEffectiveFourWaveDiagram
    {N : Nat} (diagram : EffectiveFourWaveDiagram N) : Prop :=
  IsTwoVertexMomentumSupported diagram ∧
    ∀ slot : Fin 5, diagramMode diagram slot ≠ 0

instance instDecidableIsActiveEffectiveFourWaveDiagram
    {N : Nat} [NeZero N] (diagram : EffectiveFourWaveDiagram N) :
    Decidable (IsActiveEffectiveFourWaveDiagram diagram) :=
  Classical.propDecidable _

abbrev ActiveEffectiveFourWaveDiagram (N : Nat) [NeZero N] :=
  {diagram : EffectiveFourWaveDiagram N //
    IsActiveEffectiveFourWaveDiagram diagram}

noncomputable instance activeEffectiveFourWaveDiagramFintype
    (N : Nat) [NeZero N] : Fintype (ActiveEffectiveFourWaveDiagram N) :=
  Fintype.ofFinite _

theorem innerSignedFourierTriple_active
    {N : Nat} [NeZero N] (diagram : ActiveEffectiveFourWaveDiagram N) :
    IsNonzeroMomentumTriple (innerSignedFourierTriple diagram.1) := by
  constructor
  · intro slot
    fin_cases slot
    · exact diagram.2.2 1
    · exact diagram.2.2 3
    · exact diagram.2.2 4
  · exact innerTriple_momentumBalanced_of_supported diagram.1 diagram.2.1

theorem innerHomologicalDivisor_ne_zero
    {N : Nat} [NeZero N] (diagram : ActiveEffectiveFourWaveDiagram N) :
    innerHomologicalDivisor diagram.1 ≠ 0 := by
  unfold innerHomologicalDivisor phaseSignActReal
  apply mul_ne_zero
  · cases insertedBranch diagram.1 <;> norm_num
  · exact signedFourierTripleMismatch_ne_zero_of_nonzeroMomentum
      (innerSignedFourierTriple diagram.1)
      (innerSignedFourierTriple_active diagram)

theorem finiteThreeWaveGap_le_abs_innerHomologicalDivisor
    {N : Nat} [NeZero N] (diagram : ActiveEffectiveFourWaveDiagram N) :
    finiteNonzeroMomentumThreeWaveGap N ≤
      |innerHomologicalDivisor diagram.1| := by
  unfold innerHomologicalDivisor phaseSignActReal
  rw [abs_mul]
  have hsign : |((insertedBranch diagram.1).exponent : Real)| = 1 := by
    cases insertedBranch diagram.1 <;> norm_num
  rw [hsign, one_mul]
  exact finiteNonzeroMomentumThreeWaveGap_le N
    (innerSignedFourierTriple diagram.1)
    (innerSignedFourierTriple_active diagram)

/-! ## The two-alpha numerator and homological four-wave vertex -/

/-- Fourier momentum placed in the left input of the outer convolution.  The
other input is determined by `output - left`; the insertion slot decides
whether the intermediate or spectator branch is placed first. -/
def outerVertexLeftMomentum
    {N : Nat} (diagram : EffectiveFourWaveDiagram N) : Site N :=
  if outerInsertionSlot diagram = 0 then
    phaseSignedMomentum (insertedBranch diagram) (intermediateMomentum diagram)
  else
    phaseSignedMomentum (spectatorBranch diagram) (spectatorMomentum diagram)

def outerQuadraticVertexCoefficient
    (N : Nat) [NeZero N] (alpha : Real)
    (diagram : EffectiveFourWaveDiagram N) : Complex :=
  pureAlphaQuadraticFourierCoefficient N alpha
    (outputMomentum diagram) (outerVertexLeftMomentum diagram)

def innerQuadraticVertexCoefficient
    (N : Nat) [NeZero N] (alpha : Real)
    (diagram : EffectiveFourWaveDiagram N) : Complex :=
  pureAlphaQuadraticFourierCoefficient N alpha
    (intermediateMomentum diagram)
    (phaseSignedMomentum (innerLeftBranch diagram) (innerLeftMomentum diagram))

/-- Product of the two microscopic quadratic coefficients.  If the inserted
outer branch is conjugate, the inner coefficient is conjugated as required by
differentiating that branch. -/
def twoVertexNumerator
    (N : Nat) [NeZero N] (alpha : Real)
    (diagram : EffectiveFourWaveDiagram N) : Complex :=
  outerQuadraticVertexCoefficient N alpha diagram *
    phaseSignActComplex (insertedBranch diagram)
      (innerQuadraticVertexCoefficient N alpha diagram)

/-- Effective four-wave coefficient after division by the nonresonant inner
homological divisor. -/
def effectiveFourWaveCoefficient
    (N : Nat) [NeZero N] (alpha : Real)
    (diagram : EffectiveFourWaveDiagram N) : Complex :=
  twoVertexNumerator N alpha diagram /
    (Complex.I * innerHomologicalDivisor diagram)

theorem pureAlphaQuadraticFourierCoefficient_scale
    (N : Nat) [NeZero N] (alpha : Real) (output left : Site N) :
    pureAlphaQuadraticFourierCoefficient N alpha output left =
      (alpha : Complex) *
        pureAlphaQuadraticFourierCoefficient N 1 output left := by
  simp [pureAlphaQuadraticFourierCoefficient]
  ring

theorem phaseSignActComplex_real_mul
    (sign : PhaseSign) (alpha : Real) (value : Complex) :
    phaseSignActComplex sign ((alpha : Complex) * value) =
      (alpha : Complex) * phaseSignActComplex sign value := by
  cases sign <;> simp [phaseSignActComplex]

/-- Each two-vertex numerator carries exactly two factors of the microscopic
alpha coupling. -/
theorem twoVertexNumerator_eq_alpha_sq_mul_unit
    (N : Nat) [NeZero N] (alpha : Real)
    (diagram : EffectiveFourWaveDiagram N) :
    twoVertexNumerator N alpha diagram =
      (alpha : Complex) ^ 2 * twoVertexNumerator N 1 diagram := by
  unfold twoVertexNumerator outerQuadraticVertexCoefficient
    innerQuadraticVertexCoefficient
  have houter := pureAlphaQuadraticFourierCoefficient_scale N alpha
    (outputMomentum diagram) (outerVertexLeftMomentum diagram)
  have hinner := pureAlphaQuadraticFourierCoefficient_scale N alpha
    (intermediateMomentum diagram)
    (phaseSignedMomentum (innerLeftBranch diagram) (innerLeftMomentum diagram))
  rw [houter, hinner, phaseSignActComplex_real_mul]
  ring

theorem effectiveFourWaveCoefficient_eq_alpha_sq_mul_unit
    (N : Nat) [NeZero N] (alpha : Real)
    (diagram : EffectiveFourWaveDiagram N) :
    effectiveFourWaveCoefficient N alpha diagram =
      (alpha : Complex) ^ 2 * effectiveFourWaveCoefficient N 1 diagram := by
  unfold effectiveFourWaveCoefficient
  rw [twoVertexNumerator_eq_alpha_sq_mul_unit]
  ring

theorem twoVertexNumerator_eq_zero_of_output_zero
    (N : Nat) [NeZero N] (alpha : Real)
    (diagram : EffectiveFourWaveDiagram N)
    (hzero : outputMomentum diagram = 0) :
    twoVertexNumerator N alpha diagram = 0 := by
  simp [twoVertexNumerator, outerQuadraticVertexCoefficient, hzero]

theorem twoVertexNumerator_eq_zero_of_intermediate_zero
    (N : Nat) [NeZero N] (alpha : Real)
    (diagram : EffectiveFourWaveDiagram N)
    (hzero : intermediateMomentum diagram = 0) :
    twoVertexNumerator N alpha diagram = 0 := by
  have hinner : innerQuadraticVertexCoefficient N alpha diagram = 0 := by
    simp [innerQuadraticVertexCoefficient, hzero]
  rw [twoVertexNumerator, hinner]
  cases insertedBranch diagram <;> simp [phaseSignActComplex]

theorem twoVertexNumerator_eq_zero_of_innerLeft_zero
    (N : Nat) [NeZero N] (alpha : Real)
    (diagram : EffectiveFourWaveDiagram N)
    (hzero : innerLeftMomentum diagram = 0) :
    twoVertexNumerator N alpha diagram = 0 := by
  have hinner : innerQuadraticVertexCoefficient N alpha diagram = 0 := by
    simp [innerQuadraticVertexCoefficient, hzero]
  rw [twoVertexNumerator, hinner]
  cases insertedBranch diagram <;> simp [phaseSignActComplex]

theorem twoVertexNumerator_eq_zero_of_innerRight_zero
    (N : Nat) [NeZero N] (alpha : Real)
    (diagram : EffectiveFourWaveDiagram N)
    (hsupported : IsTwoVertexMomentumSupported diagram)
    (hzero : innerRightMomentum diagram = 0) :
    twoVertexNumerator N alpha diagram = 0 := by
  unfold IsTwoVertexMomentumSupported at hsupported
  have hleft :
      phaseSignedMomentum (innerLeftBranch diagram) (innerLeftMomentum diagram) =
        intermediateMomentum diagram := by
    rw [hzero] at hsupported
    simpa using hsupported.2.symm
  have hinner : innerQuadraticVertexCoefficient N alpha diagram = 0 := by
    simp [innerQuadraticVertexCoefficient, hleft]
  rw [twoVertexNumerator, hinner]
  cases insertedBranch diagram <;> simp [phaseSignActComplex]

theorem twoVertexNumerator_eq_zero_of_spectator_zero
    (N : Nat) [NeZero N] (alpha : Real)
    (diagram : EffectiveFourWaveDiagram N)
    (hsupported : IsTwoVertexMomentumSupported diagram)
    (hzero : spectatorMomentum diagram = 0) :
    twoVertexNumerator N alpha diagram = 0 := by
  unfold IsTwoVertexMomentumSupported at hsupported
  by_cases hslot : outerInsertionSlot diagram = 0
  · have hinserted :
        phaseSignedMomentum (insertedBranch diagram) (intermediateMomentum diagram) =
          outputMomentum diagram := by
      rw [hzero] at hsupported
      simpa using hsupported.1.symm
    simp [twoVertexNumerator, outerQuadraticVertexCoefficient,
      outerVertexLeftMomentum, hslot, hinserted]
  · simp [twoVertexNumerator, outerQuadraticVertexCoefficient,
      outerVertexLeftMomentum, hslot, hzero]

/-- Every zero external four-wave leg kills the two-vertex coefficient. -/
theorem twoVertexNumerator_eq_zero_of_external_zero
    (N : Nat) [NeZero N] (alpha : Real)
    (diagram : EffectiveFourWaveDiagram N)
    (hsupported : IsTwoVertexMomentumSupported diagram)
    (hzero : ∃ slot : Fin 4, totalFourWaveModes diagram slot = 0) :
    twoVertexNumerator N alpha diagram = 0 := by
  obtain ⟨slot, hslot⟩ := hzero
  fin_cases slot
  · exact twoVertexNumerator_eq_zero_of_output_zero N alpha diagram hslot
  · exact twoVertexNumerator_eq_zero_of_spectator_zero
      N alpha diagram hsupported hslot
  · exact twoVertexNumerator_eq_zero_of_innerLeft_zero N alpha diagram hslot
  · exact twoVertexNumerator_eq_zero_of_innerRight_zero
      N alpha diagram hsupported hslot

theorem effectiveFourWaveCoefficient_eq_zero_of_external_zero
    (N : Nat) [NeZero N] (alpha : Real)
    (diagram : EffectiveFourWaveDiagram N)
    (hsupported : IsTwoVertexMomentumSupported diagram)
    (hzero : ∃ slot : Fin 4, totalFourWaveModes diagram slot = 0) :
    effectiveFourWaveCoefficient N alpha diagram = 0 := by
  unfold effectiveFourWaveCoefficient
  rw [twoVertexNumerator_eq_zero_of_external_zero
    N alpha diagram hsupported hzero]
  simp

/-! ## Exact finite nested extraction -/

def activeTwoVertexNumerator
    (N : Nat) [NeZero N] (alpha : Real) :
    ActiveEffectiveFourWaveDiagram N → Complex :=
  fun diagram ↦ twoVertexNumerator N alpha diagram.1

def activeOuterThreeWaveMismatch
    (N : Nat) [NeZero N] : ActiveEffectiveFourWaveDiagram N → Real :=
  fun diagram ↦ outerThreeWaveMismatch diagram.1

def activeInnerHomologicalDivisor
    (N : Nat) [NeZero N] : ActiveEffectiveFourWaveDiagram N → Real :=
  fun diagram ↦ innerHomologicalDivisor diagram.1

/-- Exact order-two nested term split into its effective four-wave part and
the first-normal-form boundary term. -/
theorem activeNestedPicardSum_eq_effective_sub_boundary
    (N : Nat) [NeZero N] (alpha : Real) (time : Real) :
    finiteNestedPicardSum
        (activeTwoVertexNumerator N alpha)
        (activeOuterThreeWaveMismatch N)
        (activeInnerHomologicalDivisor N) time =
      finiteEffectiveInteractionSum
          (activeTwoVertexNumerator N alpha)
          (activeOuterThreeWaveMismatch N)
          (activeInnerHomologicalDivisor N) time -
        finiteNormalFormBoundarySum
          (activeTwoVertexNumerator N alpha)
          (activeOuterThreeWaveMismatch N)
          (activeInnerHomologicalDivisor N) time := by
  exact finiteNestedPicardSum_eq_effective_sub_boundary
    (activeTwoVertexNumerator N alpha)
    (activeOuterThreeWaveMismatch N)
    (activeInnerHomologicalDivisor N) time
    (fun diagram ↦ innerHomologicalDivisor_ne_zero diagram)

/-- The effective term exposed by nested extraction is literally the sum of
the homological four-wave coefficient against the total four-wave phase. -/
theorem activeFiniteEffectiveInteractionSum_eq_fourWaveVertexSum
    (N : Nat) [NeZero N] (alpha : Real) (time : Real) :
    finiteEffectiveInteractionSum
        (activeTwoVertexNumerator N alpha)
        (activeOuterThreeWaveMismatch N)
        (activeInnerHomologicalDivisor N) time =
      ∑ diagram : ActiveEffectiveFourWaveDiagram N,
        effectiveFourWaveCoefficient N alpha diagram.1 *
          oscillatoryIntegral (totalFourWaveMismatch diagram.1) time := by
  unfold finiteEffectiveInteractionSum activeTwoVertexNumerator
    activeOuterThreeWaveMismatch activeInnerHomologicalDivisor
    effectiveFourWaveCoefficient
  apply Finset.sum_congr rfl
  intro diagram _hdiagram
  rw [outer_add_innerHomologicalDivisor_eq_totalFourWaveMismatch]

/-- Fully resolved exact split, with the dangerous total four-wave phase
retained rather than treated as an error. -/
theorem activeNestedPicardSum_eq_fourWaveVertexSum_sub_boundary
    (N : Nat) [NeZero N] (alpha : Real) (time : Real) :
    finiteNestedPicardSum
        (activeTwoVertexNumerator N alpha)
        (activeOuterThreeWaveMismatch N)
        (activeInnerHomologicalDivisor N) time =
      (∑ diagram : ActiveEffectiveFourWaveDiagram N,
        effectiveFourWaveCoefficient N alpha diagram.1 *
          oscillatoryIntegral (totalFourWaveMismatch diagram.1) time) -
        finiteNormalFormBoundarySum
          (activeTwoVertexNumerator N alpha)
          (activeOuterThreeWaveMismatch N)
          (activeInnerHomologicalDivisor N) time := by
  rw [activeNestedPicardSum_eq_effective_sub_boundary,
    activeFiniteEffectiveInteractionSum_eq_fourWaveVertexSum]

/-- Fixed-volume endpoint control using the existing nonzero three-wave gap.
The gap is not asserted to be uniform in `N`. -/
theorem norm_activeFiniteNormalFormBoundarySum_le_fixedThreeWaveGap
    (N : Nat) [NeZero N] (alpha : Real) (time : Real) :
    ‖finiteNormalFormBoundarySum
        (activeTwoVertexNumerator N alpha)
        (activeOuterThreeWaveMismatch N)
        (activeInnerHomologicalDivisor N) time‖ ≤
      (|time| / finiteNonzeroMomentumThreeWaveGap N) *
        ∑ diagram : ActiveEffectiveFourWaveDiagram N,
          ‖activeTwoVertexNumerator N alpha diagram‖ := by
  exact norm_finiteNormalFormBoundarySum_le
    (activeTwoVertexNumerator N alpha)
    (activeOuterThreeWaveMismatch N)
    (activeInnerHomologicalDivisor N) time
    (finiteNonzeroMomentumThreeWaveGap N)
    (finiteNonzeroMomentumThreeWaveGap_pos N)
    (fun diagram ↦ finiteThreeWaveGap_le_abs_innerHomologicalDivisor diagram)

end

end ArchonPhysics.EqualMassPeriodicFPUTEffectiveFourWaveVertex
