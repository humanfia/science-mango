import ArchonPhysics.EqualMassPeriodicFPUTBranchMomentumRelabel
import ArchonPhysics.QuadraticInteractionFirstNormalForm

/-!
# The actual periodic alpha-FPUT trajectory after one normal-form step

This module packages every nonzero signed Fourier branch of an actual
Physlib alpha-FPUT trajectory as one finite mode family.  The exact
interaction-picture convolution is identified with the generic quadratic
oscillatory source, so the first normal-form theorem applies to the real
Hamiltonian trajectory rather than to an abstract assumed path.

Unsupported pairs receive zero vertex and an arbitrary positive fixed-volume
phase (the already-proved finite three-wave gap).  This totalizes the generic
finite-mode API without changing the source and permits its global gap
hypothesis to be discharged.  Nothing here is uniform in the volume, and no
random-phase or kinetic statement is made.
-/

namespace ArchonPhysics.EqualMassPeriodicFPUTActualFirstNormalForm

open scoped BigOperators

open ArchonPhysics
open ArchonPhysics.CoerciveHamiltonianPhyslib
open ArchonPhysics.ComplexFourierBranchAmplitude
open ArchonPhysics.EqualMassPeriodicFPUTBranchMomentumRelabel
open ArchonPhysics.EqualMassPeriodicFPUTFourierHamiltonian
open ArchonPhysics.EqualMassPeriodicFPUTFourierThreeWave
open ArchonPhysics.EqualMassPeriodicFPUTInteractionPicture
open ArchonPhysics.FinitePhaseMonomials
open ArchonPhysics.FreeFPUTTensorPhaseExpansion
open ArchonPhysics.Lattice
open ArchonPhysics.PhaseRenormalization
open ArchonPhysics.QuadraticInteractionFirstNormalForm
open Time

noncomputable section

/-! ## A finite family containing exactly the nonzero signed branches -/

/-- Nontranslation Fourier indices. -/
abbrev NonzeroFourierMode (N : Nat) := {mode : Site N // mode ≠ 0}

/-- One of the two interaction-picture branches over a nonzero Fourier
index.  `Fin 2` is used so the family inherits the canonical finite type. -/
abbrev ActualInteractionBranchMode (N : Nat) :=
  Fin 2 × NonzeroFourierMode N

def actualBranchSign {N : Nat}
    (mode : ActualInteractionBranchMode N) : PhaseSign :=
  binaryPhaseSign mode.1

def actualBranchRawMode {N : Nat}
    (mode : ActualInteractionBranchMode N) : Site N :=
  mode.2.1

@[simp] theorem actualBranchRawMode_ne_zero
    {N : Nat} (mode : ActualInteractionBranchMode N) :
    actualBranchRawMode mode ≠ 0 :=
  mode.2.2

/-- The actual signed interaction-picture trajectory, restricted only by
removing the translation mode whose oscillator normalization vanishes. -/
def actualInteractionBranchPath
    {N : Nat} [NeZero N]
    (p q : Time → HilbertConfiguration N) :
    Real → ActualInteractionBranchMode N → Complex :=
  fun tau mode ↦ equalMassInteractionBranch
    (actualBranchSign mode) (actualBranchRawMode mode) p q tau

/-! ## A totalized quadratic source with zero inactive vertices -/

def ActualQuadraticMomentumSupported
    {N : Nat} (out left right : ActualInteractionBranchMode N) : Prop :=
  actualBranchRawMode out =
    actualBranchRawMode left + actualBranchRawMode right

instance actualQuadraticMomentumSupportedDecidable
    {N : Nat} (out left right : ActualInteractionBranchMode N) :
    Decidable (ActualQuadraticMomentumSupported out left right) := by
  unfold ActualQuadraticMomentumSupported
  infer_instance

/-- The real unit-coupling FPUT vertex on a supported convolution pair and
zero elsewhere. -/
def actualQuadraticVertex
    (N : Nat) [NeZero N] (alpha : Real)
    (out left right : ActualInteractionBranchMode N) : Complex := by
  classical
  exact if ActualQuadraticMomentumSupported out left right then
      equalMassQuadraticBranchVertex alpha
        (actualBranchRawMode out) (actualBranchRawMode left)
        (actualBranchSign out)
    else 0

/-- The actual branch mismatch on supported pairs.  On zero-vertex pairs its
value is fixed to the positive finite-volume gap, which is analytically
irrelevant but supplies the total generic API with a global nonzero phase. -/
def actualQuadraticMismatch
    (N : Nat) [NeZero N]
    (out left right : ActualInteractionBranchMode N) : Real := by
  classical
  exact if ActualQuadraticMomentumSupported out left right then
      equalMassQuadraticBranchMismatch
        (actualBranchRawMode out) (actualBranchRawMode left)
        (actualBranchSign out) (actualBranchSign left) (actualBranchSign right)
    else finiteNonzeroMomentumThreeWaveGap N

theorem actualQuadraticMismatch_eq_of_supported
    {N : Nat} [NeZero N]
    {out left right : ActualInteractionBranchMode N}
    (hsupported : ActualQuadraticMomentumSupported out left right) :
    actualQuadraticMismatch N out left right =
      equalMassQuadraticBranchMismatch
        (actualBranchRawMode out) (actualBranchRawMode left)
        (actualBranchSign out) (actualBranchSign left)
        (actualBranchSign right) := by
  simp [actualQuadraticMismatch, hsupported]

theorem actualQuadraticVertex_eq_of_supported
    {N : Nat} [NeZero N] (alpha : Real)
    {out left right : ActualInteractionBranchMode N}
    (hsupported : ActualQuadraticMomentumSupported out left right) :
    actualQuadraticVertex N alpha out left right =
      equalMassQuadraticBranchVertex alpha
        (actualBranchRawMode out) (actualBranchRawMode left)
        (actualBranchSign out) := by
  simp [actualQuadraticVertex, hsupported]

theorem rightRawMode_eq_output_sub_left_of_supported
    {N : Nat} {out left right : ActualInteractionBranchMode N}
    (hsupported : ActualQuadraticMomentumSupported out left right) :
    actualBranchRawMode right =
      actualBranchRawMode out - actualBranchRawMode left := by
  unfold ActualQuadraticMomentumSupported at hsupported
  rw [hsupported]
  abel

/-! ## Fixed-volume nonresonance and coupling homogeneity -/

theorem finiteGap_le_abs_actualQuadraticMismatch
    (N : Nat) [NeZero N]
    (out left right : ActualInteractionBranchMode N) :
    finiteNonzeroMomentumThreeWaveGap N ≤
      |actualQuadraticMismatch N out left right| := by
  by_cases hsupported : ActualQuadraticMomentumSupported out left right
  · rw [actualQuadraticMismatch_eq_of_supported hsupported]
    have hright := rightRawMode_eq_output_sub_left_of_supported hsupported
    exact finiteNonzeroMomentumThreeWaveGap_le_branchMismatch
      (actualBranchSign out) (actualBranchSign left) (actualBranchSign right)
      (actualBranchRawMode_ne_zero out)
      (actualBranchRawMode_ne_zero left)
      (by rw [← hright]; exact actualBranchRawMode_ne_zero right)
  · rw [show actualQuadraticMismatch N out left right =
        finiteNonzeroMomentumThreeWaveGap N by
      simp [actualQuadraticMismatch, hsupported]]
    rw [abs_of_pos (finiteNonzeroMomentumThreeWaveGap_pos N)]

theorem actualQuadraticMismatch_ne_zero
    (N : Nat) [NeZero N]
    (out left right : ActualInteractionBranchMode N) :
    actualQuadraticMismatch N out left right ≠ 0 := by
  intro hzero
  have hgap := finiteGap_le_abs_actualQuadraticMismatch N out left right
  rw [hzero, abs_zero] at hgap
  exact (not_lt_of_ge hgap) (finiteNonzeroMomentumThreeWaveGap_pos N)

theorem equalMassQuadraticBranchVertex_scale
    (N : Nat) [NeZero N] (alpha : Real) (k l : Site N)
    (outputSign : PhaseSign) :
    equalMassQuadraticBranchVertex alpha k l outputSign =
      (alpha : Complex) *
        equalMassQuadraticBranchVertex 1 k l outputSign := by
  unfold equalMassQuadraticBranchVertex
    pureAlphaQuadraticFourierCoefficient
  push_cast
  ring

theorem actualQuadraticVertex_scale
    (N : Nat) [NeZero N] (alpha : Real)
    (out left right : ActualInteractionBranchMode N) :
    actualQuadraticVertex N alpha out left right =
      (alpha : Complex) * actualQuadraticVertex N 1 out left right := by
  by_cases hsupported : ActualQuadraticMomentumSupported out left right
  · simp only [actualQuadraticVertex, if_pos hsupported]
    exact equalMassQuadraticBranchVertex_scale N alpha
      (actualBranchRawMode out) (actualBranchRawMode left)
      (actualBranchSign out)
  · simp [actualQuadraticVertex, hsupported]

/-! ## Finite reindexing of the literal convolution -/

theorem sum_binaryPhaseSign_eq_phaseSignFinset
    (f : PhaseSign → Complex) :
    (∑ sign : Fin 2, f (binaryPhaseSign sign)) =
      ∑ sign ∈ phaseSignFinset, f sign := by
  rw [Fin.sum_univ_two]
  simp [phaseSignFinset]

private theorem sum_nonzero_right_selector
    {N : Nat} [NeZero N] (k l : Site N)
    (f : NonzeroFourierMode N → Complex) :
    (∑ right : NonzeroFourierMode N,
        if k = l + right.1 then f right else 0) =
      if hright : k - l ≠ 0 then
        f ⟨k - l, hright⟩
      else 0 := by
  classical
  by_cases hright : k - l ≠ 0
  · rw [dif_pos hright]
    let target : NonzeroFourierMode N := ⟨k - l, hright⟩
    rw [Fintype.sum_eq_single target]
    · simp [target]
    · intro other hne
      rw [if_neg]
      intro heq
      apply hne
      apply Subtype.ext
      change other.1 = k - l
      rw [heq]
      abel
  · rw [dif_neg hright]
    apply Finset.sum_eq_zero
    intro right _hrightMem
    rw [if_neg]
    intro heq
    apply right.property
    have : right.1 = k - l := by
      rw [heq]
      abel
    rw [this, not_ne_iff.mp hright]

private theorem sum_nonzero_left_filter
    {N : Nat} [NeZero N] (k : Site N)
    (f : Site N → Complex) :
    (∑ left : NonzeroFourierMode N,
        if k - left.1 ≠ 0 then f left.1 else 0) =
      ∑ l ∈ nonzeroInputMomenta N k, f l := by
  classical
  calc
    (∑ left : NonzeroFourierMode N,
        if k - left.1 ≠ 0 then f left.1 else 0) =
        ∑ l ∈ (Finset.univ.filter fun l : Site N ↦ l ≠ 0),
          if k - l ≠ 0 then f l else 0 := by
      symm
      exact Finset.sum_subtype _ (by intro l; simp) _
    _ = ∑ l : Site N,
        if l ≠ 0 then (if k - l ≠ 0 then f l else 0) else 0 := by
      rw [Finset.sum_filter]
    _ = ∑ l : Site N,
        if l ≠ 0 ∧ k - l ≠ 0 then f l else 0 := by
      apply Finset.sum_congr rfl
      intro l _hl
      by_cases hleft : l ≠ 0 <;>
        by_cases hright : k - l ≠ 0 <;>
        simp [hleft, hright]
    _ = ∑ l ∈ nonzeroInputMomenta N k, f l := by
      unfold nonzeroInputMomenta
      rw [Finset.sum_filter]

/-! ## Exact identification with the generic quadratic source -/

private theorem genericQuadraticSummand_eq_branchTerm_of_supported
    {N : Nat} [NeZero N] (alpha : Real)
    (p q : Time → HilbertConfiguration N) (tau : Real)
    {out left right : ActualInteractionBranchMode N}
    (hsupported : ActualQuadraticMomentumSupported out left right) :
    actualQuadraticVertex N alpha out left right *
        Complex.exp ((Complex.I * actualQuadraticMismatch N out left right) * tau) *
        actualInteractionBranchPath p q tau left *
        actualInteractionBranchPath p q tau right =
      equalMassQuadraticBranchTerm alpha
        (actualBranchRawMode out) (actualBranchRawMode left)
        (actualBranchSign out) (actualBranchSign left) (actualBranchSign right)
        p q tau := by
  rw [actualQuadraticVertex_eq_of_supported alpha hsupported,
    actualQuadraticMismatch_eq_of_supported hsupported]
  have hright := rightRawMode_eq_output_sub_left_of_supported hsupported
  unfold actualInteractionBranchPath equalMassQuadraticBranchTerm phaseFactor
  rw [hright]
  congr 1
  push_cast
  ring_nf

/-- One summand of the generic source, named to expose its zero-vertex
momentum selector. -/
def actualGenericQuadraticSummand
    {N : Nat} [NeZero N] (alpha : Real)
    (p q : Time → HilbertConfiguration N) (tau : Real)
    (out left right : ActualInteractionBranchMode N) : Complex :=
  actualQuadraticVertex N alpha out left right *
    Complex.exp ((Complex.I * actualQuadraticMismatch N out left right) * tau) *
    actualInteractionBranchPath p q tau left *
    actualInteractionBranchPath p q tau right

theorem actualGenericQuadraticSummand_eq_ite_branchTerm
    {N : Nat} [NeZero N] (alpha : Real)
    (p q : Time → HilbertConfiguration N) (tau : Real)
    (out left right : ActualInteractionBranchMode N) :
    actualGenericQuadraticSummand alpha p q tau out left right =
      if ActualQuadraticMomentumSupported out left right then
        equalMassQuadraticBranchTerm alpha
          (actualBranchRawMode out) (actualBranchRawMode left)
          (actualBranchSign out) (actualBranchSign left) (actualBranchSign right)
          p q tau
      else 0 := by
  classical
  by_cases hsupported : ActualQuadraticMomentumSupported out left right
  · rw [if_pos hsupported]
    exact genericQuadraticSummand_eq_branchTerm_of_supported
      alpha p q tau hsupported
  · simp [actualGenericQuadraticSummand, actualQuadraticVertex, hsupported]

private theorem sum_actualRight_eq_branchTerms
    {N : Nat} [NeZero N] (alpha : Real)
    (p q : Time → HilbertConfiguration N) (tau : Real)
    (out left : ActualInteractionBranchMode N) :
    (∑ right : ActualInteractionBranchMode N,
        actualGenericQuadraticSummand alpha p q tau out left right) =
      if actualBranchRawMode out - actualBranchRawMode left ≠ 0 then
        ∑ rightSign : Fin 2,
          equalMassQuadraticBranchTerm alpha
            (actualBranchRawMode out) (actualBranchRawMode left)
            (actualBranchSign out) (actualBranchSign left)
            (binaryPhaseSign rightSign) p q tau
      else 0 := by
  classical
  rw [Fintype.sum_prod_type]
  calc
    (∑ rightSign : Fin 2, ∑ right : NonzeroFourierMode N,
        actualGenericQuadraticSummand alpha p q tau out left
          (rightSign, right)) =
        ∑ rightSign : Fin 2, ∑ right : NonzeroFourierMode N,
          if actualBranchRawMode out =
              actualBranchRawMode left + right.1 then
            equalMassQuadraticBranchTerm alpha
              (actualBranchRawMode out) (actualBranchRawMode left)
              (actualBranchSign out) (actualBranchSign left)
              (binaryPhaseSign rightSign) p q tau
          else 0 := by
      apply Finset.sum_congr rfl
      intro rightSign _hrightSign
      apply Finset.sum_congr rfl
      intro right _hright
      rw [actualGenericQuadraticSummand_eq_ite_branchTerm]
      change (if actualBranchRawMode out =
          actualBranchRawMode left + right.1 then _ else _) = _
      split <;> rfl
    _ = ∑ rightSign : Fin 2,
        if hright : actualBranchRawMode out - actualBranchRawMode left ≠ 0 then
          equalMassQuadraticBranchTerm alpha
            (actualBranchRawMode out) (actualBranchRawMode left)
            (actualBranchSign out) (actualBranchSign left)
            (binaryPhaseSign rightSign) p q tau
        else 0 := by
      apply Finset.sum_congr rfl
      intro rightSign _hrightSign
      exact sum_nonzero_right_selector
        (actualBranchRawMode out) (actualBranchRawMode left)
        (fun _ ↦ equalMassQuadraticBranchTerm alpha
          (actualBranchRawMode out) (actualBranchRawMode left)
          (actualBranchSign out) (actualBranchSign left)
          (binaryPhaseSign rightSign) p q tau)
    _ = if actualBranchRawMode out - actualBranchRawMode left ≠ 0 then
        ∑ rightSign : Fin 2,
          equalMassQuadraticBranchTerm alpha
            (actualBranchRawMode out) (actualBranchRawMode left)
            (actualBranchSign out) (actualBranchSign left)
            (binaryPhaseSign rightSign) p q tau
      else 0 := by
      by_cases hright :
          actualBranchRawMode out - actualBranchRawMode left ≠ 0 <;>
        simp [hright]

/-- The generic finite quadratic source is exactly the `l × 2 × 2`
branch sum occurring in the derivative of the actual Hamiltonian trajectory. -/
theorem quadraticOscillatorySource_actual_eq_explicitBranchSum
    {N : Nat} [NeZero N] (alpha : Real)
    (p q : Time → HilbertConfiguration N) (tau : Real)
    (out : ActualInteractionBranchMode N) :
    quadraticOscillatorySource
        (actualQuadraticVertex N alpha) (actualQuadraticMismatch N)
        (actualInteractionBranchPath p q tau) tau out =
      ∑ l ∈ nonzeroInputMomenta N (actualBranchRawMode out),
        ∑ leftSign ∈ phaseSignFinset,
          ∑ rightSign ∈ phaseSignFinset,
            equalMassQuadraticBranchTerm alpha
              (actualBranchRawMode out) l
              (actualBranchSign out) leftSign rightSign p q tau := by
  classical
  unfold quadraticOscillatorySource
  rw [Fintype.sum_prod_type]
  change (∑ leftSign : Fin 2, ∑ left : NonzeroFourierMode N,
      ∑ right : ActualInteractionBranchMode N,
        actualGenericQuadraticSummand alpha p q tau out
          (leftSign, left) right) = _
  calc
    (∑ leftSign : Fin 2, ∑ left : NonzeroFourierMode N,
        ∑ right : ActualInteractionBranchMode N,
          actualGenericQuadraticSummand alpha p q tau out
            (leftSign, left) right) =
      ∑ leftSign : Fin 2, ∑ left : NonzeroFourierMode N,
        if actualBranchRawMode out - left.1 ≠ 0 then
          ∑ rightSign : Fin 2,
            equalMassQuadraticBranchTerm alpha
              (actualBranchRawMode out) left.1
              (actualBranchSign out) (binaryPhaseSign leftSign)
              (binaryPhaseSign rightSign) p q tau
        else 0 := by
      apply Finset.sum_congr rfl
      intro leftSign _hleftSign
      apply Finset.sum_congr rfl
      intro left _hleft
      exact sum_actualRight_eq_branchTerms
        alpha p q tau out (leftSign, left)
    _ = ∑ leftSign : Fin 2,
        ∑ l ∈ nonzeroInputMomenta N (actualBranchRawMode out),
          ∑ rightSign : Fin 2,
            equalMassQuadraticBranchTerm alpha
              (actualBranchRawMode out) l
              (actualBranchSign out) (binaryPhaseSign leftSign)
              (binaryPhaseSign rightSign) p q tau := by
      apply Finset.sum_congr rfl
      intro leftSign _hleftSign
      exact sum_nonzero_left_filter (actualBranchRawMode out)
        (fun l ↦ ∑ rightSign : Fin 2,
          equalMassQuadraticBranchTerm alpha
            (actualBranchRawMode out) l
            (actualBranchSign out) (binaryPhaseSign leftSign)
            (binaryPhaseSign rightSign) p q tau)
    _ = ∑ l ∈ nonzeroInputMomenta N (actualBranchRawMode out),
        ∑ leftSign : Fin 2, ∑ rightSign : Fin 2,
          equalMassQuadraticBranchTerm alpha
            (actualBranchRawMode out) l
            (actualBranchSign out) (binaryPhaseSign leftSign)
            (binaryPhaseSign rightSign) p q tau := by
      rw [Finset.sum_comm]
    _ = ∑ l ∈ nonzeroInputMomenta N (actualBranchRawMode out),
        ∑ leftSign ∈ phaseSignFinset,
          ∑ rightSign ∈ phaseSignFinset,
            equalMassQuadraticBranchTerm alpha
              (actualBranchRawMode out) l
              (actualBranchSign out) leftSign rightSign p q tau := by
      apply Finset.sum_congr rfl
      intro l _hl
      calc
        (∑ leftSign : Fin 2, ∑ rightSign : Fin 2,
            equalMassQuadraticBranchTerm alpha
              (actualBranchRawMode out) l (actualBranchSign out)
              (binaryPhaseSign leftSign) (binaryPhaseSign rightSign) p q tau) =
          ∑ leftSign ∈ phaseSignFinset, ∑ rightSign : Fin 2,
            equalMassQuadraticBranchTerm alpha
              (actualBranchRawMode out) l (actualBranchSign out)
              leftSign (binaryPhaseSign rightSign) p q tau :=
          sum_binaryPhaseSign_eq_phaseSignFinset
            (fun leftSign ↦ ∑ rightSign : Fin 2,
              equalMassQuadraticBranchTerm alpha
                (actualBranchRawMode out) l (actualBranchSign out)
                leftSign (binaryPhaseSign rightSign) p q tau)
        _ = ∑ leftSign ∈ phaseSignFinset,
            ∑ rightSign ∈ phaseSignFinset,
              equalMassQuadraticBranchTerm alpha
                (actualBranchRawMode out) l (actualBranchSign out)
                leftSign rightSign p q tau := by
          apply Finset.sum_congr rfl
          intro leftSign _hleftSign
          exact sum_binaryPhaseSign_eq_phaseSignFinset
            (fun rightSign ↦ equalMassQuadraticBranchTerm alpha
              (actualBranchRawMode out) l (actualBranchSign out)
              leftSign rightSign p q tau)

/-! ## The actual trajectory satisfies the generic quadratic equation -/

/-- The exact `l × 2 × 2` derivative of every actual nonzero branch is
the generic finite quadratic source with the physical FPUT vertex. -/
theorem hasDerivAt_actualInteractionBranch_quadraticSource
    {N : Nat} [NeZero N] (alpha : Real)
    (p q : Time → HilbertConfiguration N)
    (hHamilton :
      SatisfiesHamiltonEquations (unitMassConfig N) 1 0 alpha p q)
    (hp : Differentiable Real p) (hq : Differentiable Real q)
    (tau : Real) (out : ActualInteractionBranchMode N) :
    HasDerivAt
      (fun s ↦ actualInteractionBranchPath p q s out)
      (quadraticOscillatorySource
        (actualQuadraticVertex N alpha) (actualQuadraticMismatch N)
        (actualInteractionBranchPath p q tau) tau out) tau := by
  have hactual := hasDerivAt_equalMassInteractionBranch_explicit
    alpha (actualBranchSign out) (actualBranchRawMode out)
    p q hHamilton hp hq (actualBranchRawMode_ne_zero out) tau
  exact hactual.congr_deriv
    (quadraticOscillatorySource_actual_eq_explicitBranchSum
      alpha p q tau out).symm

/-- Pulling the scalar coupling through the finite source leaves the
unit-coupling vertex. -/
theorem quadraticOscillatorySource_actualVertex_scale
    (N : Nat) [NeZero N] (alpha : Real)
    (amplitude : ActualInteractionBranchMode N → Complex)
    (tau : Real) (out : ActualInteractionBranchMode N) :
    quadraticOscillatorySource
        (actualQuadraticVertex N alpha) (actualQuadraticMismatch N)
        amplitude tau out =
      (alpha : Complex) *
        quadraticOscillatorySource
          (actualQuadraticVertex N 1) (actualQuadraticMismatch N)
          amplitude tau out := by
  unfold quadraticOscillatorySource
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro left _hleft
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro right _hright
  rw [actualQuadraticVertex_scale]
  ring

/-- Therefore the actual Hamiltonian trajectory satisfies the unit-vertex
quadratic equation with the microscopic coupling displayed as a scalar. -/
theorem hasDerivAt_actualInteractionBranch_unitVertexSource
    {N : Nat} [NeZero N] (alpha : Real)
    (p q : Time → HilbertConfiguration N)
    (hHamilton :
      SatisfiesHamiltonEquations (unitMassConfig N) 1 0 alpha p q)
    (hp : Differentiable Real p) (hq : Differentiable Real q)
    (tau : Real) (out : ActualInteractionBranchMode N) :
    HasDerivAt
      (fun s ↦ actualInteractionBranchPath p q s out)
      ((alpha : Complex) * quadraticOscillatorySource
        (actualQuadraticVertex N 1) (actualQuadraticMismatch N)
        (actualInteractionBranchPath p q tau) tau out) tau := by
  exact (hasDerivAt_actualInteractionBranch_quadraticSource
    alpha p q hHamilton hp hq tau out).congr_deriv
      (quadraticOscillatorySource_actualVertex_scale N alpha
        (actualInteractionBranchPath p q tau) tau out)

/-! ## First normal form on the actual Physlib path -/

/-- Unit-vertex primitive which removes the order-`alpha` quadratic source. -/
def actualFirstNormalFormPrimitive
    (N : Nat) [NeZero N]
    (amplitude : ActualInteractionBranchMode N → Complex)
    (tau : Real) (out : ActualInteractionBranchMode N) : Complex :=
  quadraticPrimitiveCorrection
    (actualQuadraticVertex N 1) (actualQuadraticMismatch N)
    amplitude tau out

/-- The exact cubic feedback generated by differentiating the two input
branches in the first normal-form primitive.  It is a two-vertex,
three-free-input amplitude source, hence the effective four-wave Hamiltonian
source before any statistical closure. -/
def actualEffectiveCubicFourWaveSource
    (N : Nat) [NeZero N]
    (amplitude : ActualInteractionBranchMode N → Complex)
    (tau : Real) (out : ActualInteractionBranchMode N) : Complex :=
  quadraticCubicNormalFormSource
    (actualQuadraticVertex N 1) (actualQuadraticMismatch N)
    amplitude tau out

/-- The unit-coupling normal-form primitive obeys the existing finite-`N`
three-wave inverse-gap bound. -/
theorem norm_actualFirstNormalFormPrimitive_le_fixedGap
    (N : Nat) [NeZero N]
    (amplitude : ActualInteractionBranchMode N → Complex)
    (tau : Real) (out : ActualInteractionBranchMode N) :
    ‖actualFirstNormalFormPrimitive N amplitude tau out‖ ≤
      (2 / finiteNonzeroMomentumThreeWaveGap N) *
        ∑ left, ∑ right,
          ‖actualQuadraticVertex N 1 out left right‖ *
            ‖amplitude left‖ * ‖amplitude right‖ := by
  unfold actualFirstNormalFormPrimitive
  exact norm_quadraticPrimitiveCorrection_le
    (actualQuadraticVertex N 1) (actualQuadraticMismatch N)
    amplitude tau out
    (finiteNonzeroMomentumThreeWaveGap N)
    (finiteNonzeroMomentumThreeWaveGap_pos N)
    (fun left right ↦ finiteGap_le_abs_actualQuadraticMismatch
      N out left right)

/-- The correction as it occurs in the physical path includes one factor of
`alpha`; its boundary size has the corresponding explicit prefactor. -/
theorem norm_alpha_mul_actualFirstNormalFormPrimitive_le_fixedGap
    (N : Nat) [NeZero N] (alpha : Real)
    (amplitude : ActualInteractionBranchMode N → Complex)
    (tau : Real) (out : ActualInteractionBranchMode N) :
    ‖(alpha : Complex) * actualFirstNormalFormPrimitive N amplitude tau out‖ ≤
      |alpha| * ((2 / finiteNonzeroMomentumThreeWaveGap N) *
        ∑ left, ∑ right,
          ‖actualQuadraticVertex N 1 out left right‖ *
            ‖amplitude left‖ * ‖amplitude right‖) := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left
    (norm_actualFirstNormalFormPrimitive_le_fixedGap N amplitude tau out)
    (abs_nonneg alpha)

/-- Actual finite-volume first normal form for a differentiable Physlib
alpha-FPUT trajectory.  The order-`alpha` source is removed exactly, leaving
the displayed order-`alpha^2` effective cubic/four-wave source together with
the fixed-volume boundary bound. -/
theorem actualPhyslib_firstNormalForm
    {N : Nat} [NeZero N] (alpha : Real)
    (p q : Time → HilbertConfiguration N)
    (hHamilton :
      SatisfiesHamiltonEquations (unitMassConfig N) 1 0 alpha p q)
    (hp : Differentiable Real p) (hq : Differentiable Real q)
    (tau : Real) (out : ActualInteractionBranchMode N) :
    HasDerivAt
        (fun s ↦ actualInteractionBranchPath p q s out -
          (alpha : Complex) * actualFirstNormalFormPrimitive N
            (actualInteractionBranchPath p q s) s out)
        (-((alpha : Complex) ^ 2) * actualEffectiveCubicFourWaveSource N
          (actualInteractionBranchPath p q tau) tau out) tau ∧
      ‖(alpha : Complex) * actualFirstNormalFormPrimitive N
          (actualInteractionBranchPath p q tau) tau out‖ ≤
        |alpha| * ((2 / finiteNonzeroMomentumThreeWaveGap N) *
          ∑ left, ∑ right,
            ‖actualQuadraticVertex N 1 out left right‖ *
              ‖actualInteractionBranchPath p q tau left‖ *
              ‖actualInteractionBranchPath p q tau right‖) := by
  constructor
  · exact hasDerivAt_firstNormalForm
      (actualQuadraticVertex N 1) (actualQuadraticMismatch N)
      (actualInteractionBranchPath p q) (alpha : Complex) tau out
      (fun mode ↦ hasDerivAt_actualInteractionBranch_unitVertexSource
        alpha p q hHamilton hp hq tau mode)
  · exact norm_alpha_mul_actualFirstNormalFormPrimitive_le_fixedGap
      N alpha (actualInteractionBranchPath p q tau) tau out

@[simp] theorem actualFirstNormalFormPrimitive_zero
    (N : Nat) [NeZero N]
    (amplitude : ActualInteractionBranchMode N → Complex)
    (out : ActualInteractionBranchMode N) :
    actualFirstNormalFormPrimitive N amplitude 0 out = 0 := by
  exact quadraticPrimitiveCorrection_zero
    (actualQuadraticVertex N 1) (actualQuadraticMismatch N) amplitude out

end

end ArchonPhysics.EqualMassPeriodicFPUTActualFirstNormalForm
