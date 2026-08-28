import ArchonPhysics.EqualMassPeriodicFPUTEffectiveFourWaveVertex
import ArchonPhysics.FinitePhaseMonomialHaarOrthogonality

/-!
# Equal-mass alpha-FPUT four-wave diagrams as exact Haar phase couples

The effective two-vertex alpha-FPUT diagrams already carry four external
momenta and four interaction signs.  This module converts those collision
signs into literal phase/conjugate factors and attaches the resulting Haar
character to every active diagram.

The sign conversion is important.  `InteractionSign.plus` is a `+1` term in
the output-minus-input mismatch and therefore becomes a positive phase
factor; `InteractionSign.minus` becomes a conjugate factor.  In particular,
an input branch is reversed relative to its original `PhaseSign`, exactly as
required by the output-versus-input collision character.

Haar averaging then gives an exact finite statement: cross terms between
diagrams with different external signatures vanish, while every ordered pair
with the same signature survives.  Thus permutations and other signature
collisions are deliberately retained.  No global signature injectivity,
nonlinear RPA propagation, diagram cancellation, or kinetic limit is assumed.
-/

namespace ArchonPhysics.EqualMassPeriodicFPUTFourWaveHaarPhaseCouples

open MeasureTheory
open UnitAddTorus
open ArchonPhysics
open ArchonPhysics.EqualMassPeriodicFPUTEffectiveFourWaveVertex
open ArchonPhysics.FiniteHarmonicHaarPhasePropagation
open ArchonPhysics.FinitePhaseMonomials
open ArchonPhysics.FinitePhaseMonomialHaarOrthogonality
open ArchonPhysics.FreeFPUTCollisionMismatchBridge
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.NonresonantOscillatoryGain
open ArchonPhysics.PhyslibFPUTBinaryInteractionTreeCouples
open ArchonPhysics.RandomPhaseMoments

noncomputable section

/-! ## Four external signed factors -/

/-- Convert the sign of a term in a collision mismatch into the phase factor
with the same integer exponent. -/
def interactionSignToPhaseSign : InteractionSign → PhaseSign
  | .plus => .phase
  | .minus => .conjugate

@[simp] theorem interactionSignToPhaseSign_plus :
    interactionSignToPhaseSign .plus = .phase := rfl

@[simp] theorem interactionSignToPhaseSign_minus :
    interactionSignToPhaseSign .minus = .conjugate := rfl

/-- The integer phase exponent is the real collision-sign coefficient after
the canonical cast. -/
theorem interactionSignToPhaseSign_exponent_cast
    (sign : InteractionSign) :
    ((interactionSignToPhaseSign sign).exponent : Real) =
      sign.coefficient := by
  cases sign <;>
    simp [interactionSignToPhaseSign, PhaseSign.exponent,
      InteractionSign.coefficient]

/-- An input collision sign reverses the original phase branch.  This is the
explicit convention bridge used for spectator and inner external legs. -/
theorem interactionSignToPhaseSign_input
    (sign : PhaseSign) :
    interactionSignToPhaseSign (phaseSignToInputInteractionSign sign) =
      composePhaseSign .conjugate sign := by
  cases sign <;>
    rfl

@[simp] theorem composePhaseSign_phase_right (sign : PhaseSign) :
    composePhaseSign sign .phase = sign := by
  cases sign <;>
    rfl

@[simp] theorem composePhaseSign_phase_left (sign : PhaseSign) :
    composePhaseSign .phase sign = sign := rfl

/-- The signed phase factor carried by one external four-wave leg. -/
def externalFourWaveFactor
    {N : Nat} (diagram : EffectiveFourWaveDiagram N) (slot : Fin 4) :
    SignedMode (Lattice.Site N) :=
  ⟨totalFourWaveModes diagram slot,
    interactionSignToPhaseSign (totalFourWaveSign diagram slot)⟩

/-- Literal four-factor collision monomial in the order output, spectator,
inner-left, inner-right. -/
def externalFourWaveMonomial
    {N : Nat} (diagram : EffectiveFourWaveDiagram N) :
    List (SignedMode (Lattice.Site N)) :=
  [externalFourWaveFactor diagram 0,
    externalFourWaveFactor diagram 1,
    externalFourWaveFactor diagram 2,
    externalFourWaveFactor diagram 3]

/-- Complete integer exponent signature of the four external legs. -/
def externalFourWavePhaseSignature
    {N : Nat} (diagram : EffectiveFourWaveDiagram N) :
    Lattice.Site N → Int :=
  phaseSignature (externalFourWaveMonomial diagram)

/-- Coordinate form of the signature.  It is determined only by
`totalFourWaveModes` and `totalFourWaveSign`, with repeated modes counted
with multiplicity. -/
theorem externalFourWavePhaseSignature_apply
    {N : Nat} [NeZero N] (diagram : EffectiveFourWaveDiagram N)
    (mode : Lattice.Site N) :
    externalFourWavePhaseSignature diagram mode =
      ∑ slot : Fin 4,
        if mode = totalFourWaveModes diagram slot then
          (interactionSignToPhaseSign
            (totalFourWaveSign diagram slot)).exponent
        else 0 := by
  rw [externalFourWavePhaseSignature, phaseSignature,
    monomialCharge_apply]
  simp [externalFourWaveMonomial, externalFourWaveFactor,
    Fin.sum_univ_four]
  abel

/-! ## Adapter to the existing binary-tree couple language -/

/-- A canonical binary phase tree whose four signed leaves are exactly the
external four-wave factors.  Its internal root labels are bookkeeping only;
the leaf charge is the object used below. -/
def externalFourWavePhaseTree
    {N : Nat} (diagram : EffectiveFourWaveDiagram N) :
    RandomEigenmodeBinaryTree (Lattice.Site N) :=
  .node (totalFourWaveModes diagram 0)
    (interactionSignToPhaseSign (totalFourWaveSign diagram 0)) .phase
    (.leaf (totalFourWaveModes diagram 0))
    (.node (totalFourWaveModes diagram 1)
      (interactionSignToPhaseSign (totalFourWaveSign diagram 1)) .phase
      (.leaf (totalFourWaveModes diagram 1))
      (.node (totalFourWaveModes diagram 2)
        (interactionSignToPhaseSign (totalFourWaveSign diagram 2))
        (interactionSignToPhaseSign (totalFourWaveSign diagram 3))
        (.leaf (totalFourWaveModes diagram 2))
        (.leaf (totalFourWaveModes diagram 3))))

/-- The canonical tree has literally the four factors defined from the
external arrays, in the same order. -/
theorem binaryTreeSignedLeaves_externalFourWavePhaseTree
    {N : Nat} [NeZero N] (diagram : EffectiveFourWaveDiagram N) :
    binaryTreeSignedLeaves (externalFourWavePhaseTree diagram) =
      externalFourWaveMonomial diagram := by
  unfold externalFourWavePhaseTree externalFourWaveMonomial
    externalFourWaveFactor binaryTreeSignedLeaves
  simp [binaryTreeSignedLeaves, phaseSignActSignedMode,
    composePhaseSign_phase_right, composePhaseSign_phase_left]

/-- Consequently the existing recursive binary-tree charge is exactly the
external four-wave monomial signature. -/
theorem binaryTreePhaseCharge_externalFourWavePhaseTree
    {N : Nat} [NeZero N] (diagram : EffectiveFourWaveDiagram N) :
    binaryTreePhaseCharge (externalFourWavePhaseTree diagram) =
      externalFourWavePhaseSignature diagram := by
  rw [← monomialCharge_binaryTreeSignedLeaves,
    binaryTreeSignedLeaves_externalFourWavePhaseTree]
  rfl

/-- Ordered external-tree couple associated with two effective diagrams. -/
def externalFourWaveDiagramCouple
    {N : Nat} (left right : EffectiveFourWaveDiagram N) :
    BinaryInteractionTreeCouple (Lattice.Site N) :=
  (externalFourWavePhaseTree left, externalFourWavePhaseTree right)

/-- Existing tree-couple balance is precisely equality of the two external
four-wave signatures. -/
theorem leafPhaseBalanced_externalFourWaveDiagramCouple_iff
    {N : Nat} [NeZero N]
    (left right : EffectiveFourWaveDiagram N) :
    leafPhaseBalanced (externalFourWaveDiagramCouple left right) ↔
      externalFourWavePhaseSignature left =
        externalFourWavePhaseSignature right := by
  rw [leafPhaseBalanced_iff_charge_eq]
  simp only [externalFourWaveDiagramCouple,
    binaryTreePhaseCharge_externalFourWavePhaseTree]

/-! ## Actual effective-diagram phase terms -/

/-- Deterministic finite-time coefficient of one effective four-wave diagram
after the exact inner normal-form extraction. -/
def effectiveFourWavePhaseCoefficient
    (N : Nat) [NeZero N] (alpha time : Real)
    (diagram : EffectiveFourWaveDiagram N) : Complex :=
  effectiveFourWaveCoefficient N alpha diagram *
    oscillatoryIntegral (totalFourWaveMismatch diagram) time

/-- One actual effective coefficient multiplied by its external Haar
character. -/
def effectiveFourWavePhaseTerm
    (N : Nat) [NeZero N] (alpha time : Real)
    (diagram : EffectiveFourWaveDiagram N)
    (phase : UnitAddTorus (Lattice.Site N)) : Complex :=
  weightedSignedMonomial
    (effectiveFourWavePhaseCoefficient N alpha time diagram)
    (externalFourWaveMonomial diagram) phase

/-- Ordered cross term of two actual effective diagrams. -/
def effectiveFourWavePhaseCross
    (N : Nat) [NeZero N] (alpha time : Real)
    (left right : EffectiveFourWaveDiagram N)
    (phase : UnitAddTorus (Lattice.Site N)) : Complex :=
  effectiveFourWavePhaseTerm N alpha time left phase *
    starRingEnd Complex
      (effectiveFourWavePhaseTerm N alpha time right phase)

/-- The diagram cross term is exactly the generic weighted-monomial cross
term, with no probabilistic approximation. -/
theorem effectiveFourWavePhaseCross_eq_weightedMonomialCross
    (N : Nat) [NeZero N] (alpha time : Real)
    (left right : EffectiveFourWaveDiagram N)
    (phase : UnitAddTorus (Lattice.Site N)) :
    effectiveFourWavePhaseCross N alpha time left right phase =
      weightedMonomialCross
        (effectiveFourWavePhaseCoefficient N alpha time left)
        (effectiveFourWavePhaseCoefficient N alpha time right)
        (externalFourWaveMonomial left)
        (externalFourWaveMonomial right) phase := rfl

/-- Exact pair selector.  Same-signature pairs retain their full complex
coefficient cross product; they are not reduced to the diagonal. -/
theorem integral_effectiveFourWavePhaseCross_eq_ite
    (N : Nat) [NeZero N] (alpha time : Real)
    (left right : EffectiveFourWaveDiagram N) :
    (∫ phase : UnitAddTorus (Lattice.Site N),
      effectiveFourWavePhaseCross N alpha time left right phase
      ∂finitePhaseHaarLaw (Lattice.Site N)) =
      if externalFourWavePhaseSignature left =
          externalFourWavePhaseSignature right then
        effectiveFourWavePhaseCoefficient N alpha time left *
          starRingEnd Complex
            (effectiveFourWavePhaseCoefficient N alpha time right)
      else 0 := by
  change (∫ phase : UnitAddTorus (Lattice.Site N),
      weightedMonomialCross
        (effectiveFourWavePhaseCoefficient N alpha time left)
        (effectiveFourWavePhaseCoefficient N alpha time right)
        (externalFourWaveMonomial left)
        (externalFourWaveMonomial right) phase
      ∂finitePhaseHaarLaw (Lattice.Site N)) =
    if phaseSignature (externalFourWaveMonomial left) =
        phaseSignature (externalFourWaveMonomial right) then
      effectiveFourWavePhaseCoefficient N alpha time left *
        starRingEnd Complex
          (effectiveFourWavePhaseCoefficient N alpha time right)
    else 0
  exact integral_weightedMonomialCross_eq_ite
      (effectiveFourWavePhaseCoefficient N alpha time left)
      (effectiveFourWavePhaseCoefficient N alpha time right)
      (externalFourWaveMonomial left)
      (externalFourWaveMonomial right)

/-- Different external signatures give an exactly vanishing diagram cross
expectation. -/
theorem integral_effectiveFourWavePhaseCross_eq_zero_of_signature_ne
    (N : Nat) [NeZero N] (alpha time : Real)
    (left right : EffectiveFourWaveDiagram N)
    (hsignature : externalFourWavePhaseSignature left ≠
      externalFourWavePhaseSignature right) :
    (∫ phase : UnitAddTorus (Lattice.Site N),
      effectiveFourWavePhaseCross N alpha time left right phase
      ∂finitePhaseHaarLaw (Lattice.Site N)) = 0 := by
  rw [integral_effectiveFourWavePhaseCross_eq_ite]
  exact if_neg hsignature

/-- Equivalently, every unmatched external binary-tree couple is annihilated
by Haar averaging. -/
theorem integral_effectiveFourWavePhaseCross_eq_zero_of_unmatchedCouple
    (N : Nat) [NeZero N] (alpha time : Real)
    (left right : EffectiveFourWaveDiagram N)
    (hunmatched : ¬ leafPhaseBalanced
      (externalFourWaveDiagramCouple left right)) :
    (∫ phase : UnitAddTorus (Lattice.Site N),
      effectiveFourWavePhaseCross N alpha time left right phase
      ∂finitePhaseHaarLaw (Lattice.Site N)) = 0 := by
  apply integral_effectiveFourWavePhaseCross_eq_zero_of_signature_ne
  intro hsignature
  exact hunmatched
    ((leafPhaseBalanced_externalFourWaveDiagramCouple_iff
      left right).2 hsignature)

/-- A same-signature pair, including a nontrivial permutation collision,
retains its complete coefficient cross product. -/
theorem integral_effectiveFourWavePhaseCross_eq_coefficientCross_of_signature_eq
    (N : Nat) [NeZero N] (alpha time : Real)
    (left right : EffectiveFourWaveDiagram N)
    (hsignature : externalFourWavePhaseSignature left =
      externalFourWavePhaseSignature right) :
    (∫ phase : UnitAddTorus (Lattice.Site N),
      effectiveFourWavePhaseCross N alpha time left right phase
      ∂finitePhaseHaarLaw (Lattice.Site N)) =
      effectiveFourWavePhaseCoefficient N alpha time left *
        starRingEnd Complex
          (effectiveFourWavePhaseCoefficient N alpha time right) := by
  rw [integral_effectiveFourWavePhaseCross_eq_ite, if_pos hsignature]

/-! ## Exact finite family decomposition over all active diagrams -/

/-- Sum of the actual active effective four-wave phase terms. -/
def activeEffectiveFourWaveHaarAmplitude
    (N : Nat) [NeZero N] (alpha time : Real)
    (phase : UnitAddTorus (Lattice.Site N)) : Complex :=
  finiteWeightedMonomialFamily
    (fun diagram : ActiveEffectiveFourWaveDiagram N ↦
      effectiveFourWavePhaseCoefficient N alpha time diagram.1)
    (fun diagram : ActiveEffectiveFourWaveDiagram N ↦
      externalFourWaveMonomial diagram.1) phase

/-- Exact second moment over all active diagrams.  Every ordered pair with
equal external signature is retained, including distinct diagrams related by
leg permutations. -/
theorem integral_normSq_activeEffectiveFourWaveHaarAmplitude_eq_pairSum
    (N : Nat) [NeZero N] (alpha time : Real) :
    (∫ phase : UnitAddTorus (Lattice.Site N),
      (Complex.normSq
        (activeEffectiveFourWaveHaarAmplitude N alpha time phase) : Complex)
      ∂finitePhaseHaarLaw (Lattice.Site N)) =
      ∑ left : ActiveEffectiveFourWaveDiagram N,
        ∑ right : ActiveEffectiveFourWaveDiagram N,
          if externalFourWavePhaseSignature left.1 =
              externalFourWavePhaseSignature right.1 then
            effectiveFourWavePhaseCoefficient N alpha time left.1 *
              starRingEnd Complex
                (effectiveFourWavePhaseCoefficient N alpha time right.1)
          else 0 := by
  exact integral_normSq_family_eq_equalSignaturePairSum
    (fun diagram : ActiveEffectiveFourWaveDiagram N ↦
      effectiveFourWavePhaseCoefficient N alpha time diagram.1)
    (fun diagram : ActiveEffectiveFourWaveDiagram N ↦
      externalFourWaveMonomial diagram.1)

/-- The same exact decomposition written with the existing binary-tree
couple selector.  This form makes explicit that unmatched couples vanish and
matched off-diagonal couples remain. -/
theorem integral_normSq_activeEffectiveFourWaveHaarAmplitude_eq_coupleSum
    (N : Nat) [NeZero N] (alpha time : Real) :
    (∫ phase : UnitAddTorus (Lattice.Site N),
      (Complex.normSq
        (activeEffectiveFourWaveHaarAmplitude N alpha time phase) : Complex)
      ∂finitePhaseHaarLaw (Lattice.Site N)) =
      ∑ left : ActiveEffectiveFourWaveDiagram N,
        ∑ right : ActiveEffectiveFourWaveDiagram N,
          if leafPhaseBalanced
              (externalFourWaveDiagramCouple left.1 right.1) then
            effectiveFourWavePhaseCoefficient N alpha time left.1 *
              starRingEnd Complex
                (effectiveFourWavePhaseCoefficient N alpha time right.1)
          else 0 := by
  rw [integral_normSq_activeEffectiveFourWaveHaarAmplitude_eq_pairSum]
  apply Finset.sum_congr rfl
  intro left _hleft
  apply Finset.sum_congr rfl
  intro right _hright
  by_cases hbalanced : leafPhaseBalanced
      (externalFourWaveDiagramCouple left.1 right.1)
  · have hsignature :=
      (leafPhaseBalanced_externalFourWaveDiagramCouple_iff
        left.1 right.1).1 hbalanced
    rw [if_pos hbalanced, if_pos hsignature]
  · have hsignature : externalFourWavePhaseSignature left.1 ≠
        externalFourWavePhaseSignature right.1 := by
      intro hequal
      exact hbalanced
        ((leafPhaseBalanced_externalFourWaveDiagramCouple_iff
          left.1 right.1).2 hequal)
    rw [if_neg hbalanced, if_neg hsignature]

end

end ArchonPhysics.EqualMassPeriodicFPUTFourWaveHaarPhaseCouples
