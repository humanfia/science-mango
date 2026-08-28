import ArchonPhysics.PhyslibFPUTIteratedQuadraticSecondPicardCharacterFamily
import ArchonPhysics.PhyslibHamiltonDuhamel

/-!
# Binary interaction trees and Haar couples for random-mass FPUT

This is the first finite-order tree/couple layer for the frozen v0.3
random-mass, cubic-leading FPUT model.  Since the leading modal source is
quadratic, interaction vertices are binary; no ternary NLS tree and no NLS
conclusion is imported.

The module records:

* finite rooted binary interaction shapes;
* decorations by realization-dependent normal-mode labels and phase/conjugate
  branches;
* recursive leaf charge, carried frequency, vertex mismatch, and coefficient;
* ordered tree couples and their exact leaf-charge balance selector;
* Haar annihilation of every unmatched couple at arbitrary finite order;
* exact first- and second-Picard adapters to the existing physical FPUT APIs.

All statements are finite-volume algebra.  They neither assume a kinetic
equation nor control the number or size of diagrams as the order, volume, or
time grows.
-/

namespace ArchonPhysics.PhyslibFPUTBinaryInteractionTreeCouples

open MeasureTheory
open UnitAddTorus
open ArchonPhysics
open ArchonPhysics.FiniteDuhamelPhaseAverage
open ArchonPhysics.FinitePhaseMonomials
open ArchonPhysics.FreeFPUTDuhamelResonanceBridge
open ArchonPhysics.FreeFPUTMismatchPhaseExpansion
open ArchonPhysics.FreeFPUTTensorPhaseExpansion
open ArchonPhysics.ModeCoupling
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.PhyslibFPUTFirstPicardCoordinateCharacterFamily
open ArchonPhysics.PhyslibFPUTFirstPicardDecomposition
open ArchonPhysics.PhyslibFPUTIteratedQuadraticSecondPicardCharacterFamily
open ArchonPhysics.RandomPhaseMoments

noncomputable section

/-! ## Finite binary shapes and random-eigenmode decorations -/

/-- Undecorated interaction shape.  A vertex is one insertion of the
quadratic modal source. -/
inductive BinaryInteractionTree where
  | leaf
  | node (left right : BinaryInteractionTree)
  deriving DecidableEq, Repr

namespace BinaryInteractionTree

/-- Number of quadratic interaction vertices. -/
def order : BinaryInteractionTree → Nat
  | .leaf => 0
  | .node left right => order left + order right + 1

/-- Number of free initial leaves. -/
def leafCount : BinaryInteractionTree → Nat
  | .leaf => 1
  | .node left right => leafCount left + leafCount right

theorem leafCount_eq_order_add_one (tree : BinaryInteractionTree) :
    tree.leafCount = tree.order + 1 := by
  induction tree with
  | leaf => rfl
  | node left right hleft hright =>
      simp only [leafCount, order, hleft, hright]
      omega

end BinaryInteractionTree

/-- A binary tree decorated by random-mass normal-mode labels.  Each edge
from a vertex to a child records whether that real-coordinate branch uses the
character itself or its complex conjugate. -/
inductive RandomEigenmodeBinaryTree (Mode : Type*) where
  | leaf (mode : Mode)
  | node (output : Mode) (leftSign rightSign : PhaseSign)
      (left right : RandomEigenmodeBinaryTree Mode)
  deriving Repr

namespace RandomEigenmodeBinaryTree

variable {Mode : Type*}

/-- Forget all eigenmode and sign decorations. -/
def shape : RandomEigenmodeBinaryTree Mode → BinaryInteractionTree
  | .leaf _ => .leaf
  | .node _ _ _ left right => .node left.shape right.shape

/-- Root/output mode of a decorated tree. -/
def rootMode : RandomEigenmodeBinaryTree Mode → Mode
  | .leaf mode => mode
  | .node output _ _ _ _ => output

/-- One-node-versus-leaf distinction needed when reconstructing a real
coordinate on an internal Picard edge. -/
def isLeaf : RandomEigenmodeBinaryTree Mode → Bool
  | .leaf _ => true
  | .node _ _ _ _ _ => false

@[simp] theorem shape_order_leaf (mode : Mode) :
    (shape (.leaf mode)).order = 0 := rfl

@[simp] theorem shape_order_node (output : Mode) (leftSign rightSign : PhaseSign)
    (left right : RandomEigenmodeBinaryTree Mode) :
    (shape (.node output leftSign rightSign left right)).order =
      left.shape.order + right.shape.order + 1 := rfl

end RandomEigenmodeBinaryTree

/-! ## Signed leaves and recursive phase charge -/

/-- Composition of an outer real-coordinate branch with an already signed
leaf.  `conjugate` flips the inner sign. -/
def composePhaseSign : PhaseSign → PhaseSign → PhaseSign
  | .phase, inner => inner
  | .conjugate, .phase => .conjugate
  | .conjugate, .conjugate => .phase

@[simp] theorem PhaseSign.exponent_compose
    (outer inner : PhaseSign) :
    (composePhaseSign outer inner).exponent =
      outer.exponent * inner.exponent := by
  cases outer <;> cases inner <;> rfl

/-- Action of a phase/conjugate branch on an integer charge vector. -/
def phaseSignActCharge {Mode : Type*}
    (sign : PhaseSign) (charge : Mode → Int) : Mode → Int :=
  fun mode ↦ sign.exponent * charge mode

/-- The same sign action on a real carried frequency. -/
def phaseSignActReal (sign : PhaseSign) (value : Real) : Real :=
  (sign.exponent : Real) * value

/-- The coefficient action associated with a real-coordinate branch. -/
def phaseSignActComplex (sign : PhaseSign) (value : Complex) : Complex :=
  match sign with
  | .phase => value
  | .conjugate => starRingEnd Complex value

/-- Apply an outer branch to a signed leaf occurrence. -/
def phaseSignActSignedMode {Mode : Type*}
    (outer : PhaseSign) (factor : SignedMode Mode) : SignedMode Mode :=
  ⟨factor.mode, composePhaseSign outer factor.sign⟩

theorem phaseSignActCharge_add {Mode : Type*}
    (sign : PhaseSign) (left right : Mode → Int) :
    phaseSignActCharge sign (left + right) =
      phaseSignActCharge sign left + phaseSignActCharge sign right := by
  funext mode
  simp [phaseSignActCharge]
  ring

@[simp] theorem phaseSignActCharge_phase {Mode : Type*}
    (charge : Mode → Int) :
    phaseSignActCharge .phase charge = charge := by
  funext mode
  simp [phaseSignActCharge]

@[simp] theorem phaseSignActCharge_conjugate {Mode : Type*}
    (charge : Mode → Int) :
    phaseSignActCharge .conjugate charge = -charge := by
  funext mode
  simp [phaseSignActCharge]

theorem phaseSignActSignedMode_charge
    {Mode : Type*} [DecidableEq Mode]
    (outer : PhaseSign) (factor : SignedMode Mode) :
    (phaseSignActSignedMode outer factor).charge =
      phaseSignActCharge outer factor.charge := by
  cases outer <;> cases factor with
  | mk mode sign =>
      cases sign <;>
        ext test <;>
        simp [phaseSignActSignedMode, composePhaseSign,
          phaseSignActCharge, SignedMode.charge, Pi.single_apply]

theorem monomialCharge_append
    {Mode : Type*} [DecidableEq Mode]
    (left right : List (SignedMode Mode)) :
    monomialCharge (left ++ right) =
      monomialCharge left + monomialCharge right := by
  induction left with
  | nil => simp [monomialCharge]
  | cons factor rest ih =>
      simp only [List.cons_append, monomialCharge, ih]
      abel

theorem monomialCharge_map_phaseSignActSignedMode
    {Mode : Type*} [DecidableEq Mode]
    (sign : PhaseSign) (factors : List (SignedMode Mode)) :
    monomialCharge (factors.map (phaseSignActSignedMode sign)) =
      phaseSignActCharge sign (monomialCharge factors) := by
  induction factors with
  | nil =>
      funext mode
      simp [monomialCharge, phaseSignActCharge]
  | cons factor rest ih =>
      simp only [List.map_cons, monomialCharge,
        phaseSignActSignedMode_charge, ih, phaseSignActCharge_add]

/-- Literal signed free leaves, including all repetitions. -/
def binaryTreeSignedLeaves {Mode : Type*} :
    RandomEigenmodeBinaryTree Mode → List (SignedMode Mode)
  | .leaf mode => [⟨mode, .phase⟩]
  | .node _ leftSign rightSign left right =>
      (binaryTreeSignedLeaves left).map
          (phaseSignActSignedMode leftSign) ++
        (binaryTreeSignedLeaves right).map
          (phaseSignActSignedMode rightSign)

/-- Recursive integer initial-phase charge of a decorated tree. -/
def binaryTreePhaseCharge
    {Mode : Type*} [Fintype Mode] [DecidableEq Mode] :
    RandomEigenmodeBinaryTree Mode → Mode → Int
  | .leaf mode => (SignedMode.mk mode .phase).charge
  | .node _ leftSign rightSign left right =>
      phaseSignActCharge leftSign (binaryTreePhaseCharge left) +
        phaseSignActCharge rightSign (binaryTreePhaseCharge right)

@[simp] theorem binaryTreePhaseCharge_leaf
    {Mode : Type*} [Fintype Mode] [DecidableEq Mode] (mode : Mode) :
    binaryTreePhaseCharge (.leaf mode) =
      (SignedMode.mk mode .phase).charge := rfl

@[simp] theorem binaryTreePhaseCharge_node
    {Mode : Type*} [Fintype Mode] [DecidableEq Mode]
    (output : Mode) (leftSign rightSign : PhaseSign)
    (left right : RandomEigenmodeBinaryTree Mode) :
    binaryTreePhaseCharge
        (.node output leftSign rightSign left right) =
      phaseSignActCharge leftSign (binaryTreePhaseCharge left) +
        phaseSignActCharge rightSign (binaryTreePhaseCharge right) := rfl

/-- The recursive charge is exactly the signed occurrence count of the
literal leaves. -/
theorem monomialCharge_binaryTreeSignedLeaves
    {Mode : Type*} [Fintype Mode] [DecidableEq Mode]
    (tree : RandomEigenmodeBinaryTree Mode) :
    monomialCharge (binaryTreeSignedLeaves tree) =
      binaryTreePhaseCharge tree := by
  induction tree with
  | leaf mode => simp [binaryTreeSignedLeaves, monomialCharge]
  | node output leftSign rightSign left right hleft hright =>
      simp only [binaryTreeSignedLeaves, monomialCharge_append,
        monomialCharge_map_phaseSignActSignedMode, hleft, hright,
        binaryTreePhaseCharge_node]

/-! ## Recursive carried frequency and mismatch -/

/-- Frequency carried by all signed initial leaves. -/
def binaryTreeCarriedFrequency {Mode : Type*}
    (frequency : Mode → Real) : RandomEigenmodeBinaryTree Mode → Real
  | .leaf mode => frequency mode
  | .node _ leftSign rightSign left right =>
      phaseSignActReal leftSign (binaryTreeCarriedFrequency frequency left) +
        phaseSignActReal rightSign (binaryTreeCarriedFrequency frequency right)

theorem chargeFrequency_phaseSignActCharge
    {Mode : Type*} [Fintype Mode]
    (sign : PhaseSign) (charge : Mode → Int) (frequency : Mode → Real) :
    chargeFrequency (phaseSignActCharge sign charge) frequency =
      phaseSignActReal sign (chargeFrequency charge frequency) := by
  cases sign <;>
    simp [chargeFrequency, phaseSignActCharge, phaseSignActReal,
      Finset.mul_sum]

theorem chargeFrequency_add
    {Mode : Type*} [Fintype Mode]
    (left right : Mode → Int) (frequency : Mode → Real) :
    chargeFrequency (left + right) frequency =
      chargeFrequency left frequency + chargeFrequency right frequency := by
  simp only [chargeFrequency, Pi.add_apply, Int.cast_add, add_mul,
    Finset.sum_add_distrib]

/-- Recursive carried frequency agrees with pairing the recursive integer
charge against the mode-frequency vector. -/
theorem binaryTreeCarriedFrequency_eq_chargeFrequency
    {Mode : Type*} [Fintype Mode] [DecidableEq Mode]
    (frequency : Mode → Real) (tree : RandomEigenmodeBinaryTree Mode) :
    binaryTreeCarriedFrequency frequency tree =
      chargeFrequency (binaryTreePhaseCharge tree) frequency := by
  induction tree with
  | leaf mode =>
      simp [binaryTreeCarriedFrequency, binaryTreePhaseCharge,
        chargeFrequency, SignedMode.charge, Pi.single_apply]
  | node output leftSign rightSign left right hleft hright =>
      simp only [binaryTreeCarriedFrequency, binaryTreePhaseCharge_node,
        chargeFrequency_add, chargeFrequency_phaseSignActCharge,
        hleft, hright]

/-- Total output-minus-leaf frequency mismatch of a decorated tree. -/
def binaryTreeFrequencyMismatch {Mode : Type*}
    (frequency : Mode → Real) (tree : RandomEigenmodeBinaryTree Mode) : Real :=
  frequency tree.rootMode - binaryTreeCarriedFrequency frequency tree

/-- Mismatch local to one binary vertex before adding descendant mismatch. -/
def binaryVertexMismatch {Mode : Type*}
    (frequency : Mode → Real) (output : Mode)
    (leftSign rightSign : PhaseSign) (leftMode rightMode : Mode) : Real :=
  frequency output - phaseSignActReal leftSign (frequency leftMode) -
    phaseSignActReal rightSign (frequency rightMode)

/-- Exact telescoping recursion of output-minus-leaf mismatch. -/
theorem binaryTreeFrequencyMismatch_node
    {Mode : Type*} (frequency : Mode → Real) (output : Mode)
    (leftSign rightSign : PhaseSign)
    (left right : RandomEigenmodeBinaryTree Mode) :
    binaryTreeFrequencyMismatch frequency
        (.node output leftSign rightSign left right) =
      binaryVertexMismatch frequency output leftSign rightSign
          left.rootMode right.rootMode +
        phaseSignActReal leftSign
          (binaryTreeFrequencyMismatch frequency left) +
        phaseSignActReal rightSign
          (binaryTreeFrequencyMismatch frequency right) := by
  cases leftSign <;> cases rightSign <;>
    simp [binaryTreeFrequencyMismatch, binaryVertexMismatch,
      binaryTreeCarriedFrequency, phaseSignActReal,
      RandomEigenmodeBinaryTree.rootMode] <;> ring

/-! ## Recursive deterministic coefficients -/

/-- Local data needed to evaluate a decorated binary tree.  The edge map is
allowed to distinguish a free leaf from an already integrated Picard
subtree.  This is exactly the distinction made by reconstruction of a real
coordinate: a free real coordinate contributes only its radial factor,
whereas an internal child also contributes the coordinate scale and possibly
complex conjugation. -/
structure BinaryTreeCoefficientKernel (Mode : Type*) where
  leafCoefficient : Mode → Complex
  vertexCoefficient : Mode → Mode → Mode → Complex
  edgeCoefficient : Bool → Mode → PhaseSign → Complex → Complex

/-- Deterministic coefficient obtained by recursively decorating every
vertex and edge.  Time integrals are deliberately not included. -/
def binaryTreeCoefficient {Mode : Type*}
    (kernel : BinaryTreeCoefficientKernel Mode) :
    RandomEigenmodeBinaryTree Mode → Complex
  | .leaf mode => kernel.leafCoefficient mode
  | .node output leftSign rightSign left right =>
      kernel.vertexCoefficient output left.rootMode right.rootMode *
        kernel.edgeCoefficient left.isLeaf left.rootMode leftSign
          (binaryTreeCoefficient kernel left) *
        kernel.edgeCoefficient right.isLeaf right.rootMode rightSign
          (binaryTreeCoefficient kernel right)

@[simp] theorem binaryTreeCoefficient_leaf {Mode : Type*}
    (kernel : BinaryTreeCoefficientKernel Mode) (mode : Mode) :
    binaryTreeCoefficient kernel (.leaf mode) =
      kernel.leafCoefficient mode := rfl

@[simp] theorem binaryTreeCoefficient_node {Mode : Type*}
    (kernel : BinaryTreeCoefficientKernel Mode) (output : Mode)
    (leftSign rightSign : PhaseSign)
    (left right : RandomEigenmodeBinaryTree Mode) :
    binaryTreeCoefficient kernel
        (.node output leftSign rightSign left right) =
      kernel.vertexCoefficient output left.rootMode right.rootMode *
        kernel.edgeCoefficient left.isLeaf left.rootMode leftSign
          (binaryTreeCoefficient kernel left) *
        kernel.edgeCoefficient right.isLeaf right.rootMode rightSign
          (binaryTreeCoefficient kernel right) := rfl

/-! ## Ordered couples and exact Haar selection -/

/-- The second moment pairs two independently decorated terms.  The pair is
ordered, as in the exact finite double sum; no Wick or Gaussian pairing is
inserted. -/
abbrev BinaryInteractionTreeCouple (Mode : Type*) :=
  RandomEigenmodeBinaryTree Mode × RandomEigenmodeBinaryTree Mode

/-- Exact leaf-phase balance of an ordered couple. -/
def leafPhaseBalanced {Mode : Type*} [Fintype Mode] [DecidableEq Mode]
    (couple : BinaryInteractionTreeCouple Mode) : Prop :=
  ∀ mode,
    binaryTreePhaseCharge couple.1 mode =
      binaryTreePhaseCharge couple.2 mode

instance instDecidableLeafPhaseBalanced
    {Mode : Type*} [Fintype Mode] [DecidableEq Mode]
    (couple : BinaryInteractionTreeCouple Mode) :
    Decidable (leafPhaseBalanced couple) := by
  unfold leafPhaseBalanced
  exact Fintype.decidableForallFintype

theorem leafPhaseBalanced_iff_charge_eq
    {Mode : Type*} [Fintype Mode] [DecidableEq Mode]
    (couple : BinaryInteractionTreeCouple Mode) :
    leafPhaseBalanced couple ↔
      binaryTreePhaseCharge couple.1 =
        binaryTreePhaseCharge couple.2 := by
  constructor
  · exact fun h ↦ funext h
  · exact fun h mode ↦ congrFun h mode

/-- Executable selector for the exact balance predicate. -/
def leafPhaseBalanceSelector {Mode : Type*}
    [Fintype Mode] [DecidableEq Mode]
    (couple : BinaryInteractionTreeCouple Mode) : Bool :=
  decide (leafPhaseBalanced couple)

theorem leafPhaseBalanceSelector_eq_true_iff
    {Mode : Type*} [Fintype Mode] [DecidableEq Mode]
    (couple : BinaryInteractionTreeCouple Mode) :
    leafPhaseBalanceSelector couple = true ↔ leafPhaseBalanced couple := by
  simp [leafPhaseBalanceSelector]

/-- Unit coefficient character carried by one complete tree. -/
def binaryTreeCharacter {Mode : Type*}
    [Fintype Mode] [DecidableEq Mode]
    (tree : RandomEigenmodeBinaryTree Mode)
    (phase : UnitAddTorus Mode) : Complex :=
  mFourier (binaryTreePhaseCharge tree) phase

/-- Character product appearing in the ordered tree-couple second moment. -/
def binaryTreeCoupleCharacter {Mode : Type*}
    [Fintype Mode] [DecidableEq Mode]
    (couple : BinaryInteractionTreeCouple Mode)
    (phase : UnitAddTorus Mode) : Complex :=
  binaryTreeCharacter couple.1 phase *
    starRingEnd Complex (binaryTreeCharacter couple.2 phase)

theorem binaryTreeCoupleCharacter_eq_differenceCharacter
    {Mode : Type*} [Fintype Mode] [DecidableEq Mode]
    (couple : BinaryInteractionTreeCouple Mode)
    (phase : UnitAddTorus Mode) :
    binaryTreeCoupleCharacter couple phase =
      mFourier
        (binaryTreePhaseCharge couple.1 -
          binaryTreePhaseCharge couple.2) phase := by
  exact mFourier_mul_star_mFourier
    (binaryTreePhaseCharge couple.1)
    (binaryTreePhaseCharge couple.2) phase

/-- At every finite pair of orders, Haar averaging retains exactly the
leaf-charge-balanced couples. -/
theorem integral_binaryTreeCoupleCharacter_eq_ite
    {Mode : Type*} [Fintype Mode] [DecidableEq Mode]
    (couple : BinaryInteractionTreeCouple Mode) :
    (∫ phase : UnitAddTorus Mode,
      binaryTreeCoupleCharacter couple phase ∂finitePhaseHaarLaw Mode) =
      if leafPhaseBalanced couple then 1 else 0 := by
  rw [show (fun phase ↦ binaryTreeCoupleCharacter couple phase) =
      fun phase ↦ mFourier
        (binaryTreePhaseCharge couple.1 -
          binaryTreePhaseCharge couple.2) phase by
      funext phase
      exact binaryTreeCoupleCharacter_eq_differenceCharacter couple phase]
  rw [integral_mFourier_eq_ite]
  by_cases hbalanced : leafPhaseBalanced couple
  · have heq := (leafPhaseBalanced_iff_charge_eq couple).mp hbalanced
    rw [if_pos hbalanced, if_pos (sub_eq_zero.mpr heq)]
  · have hne :
        binaryTreePhaseCharge couple.1 -
            binaryTreePhaseCharge couple.2 ≠ 0 := by
      intro hzero
      apply hbalanced
      exact (leafPhaseBalanced_iff_charge_eq couple).mpr
        (sub_eq_zero.mp hzero)
    rw [if_neg hbalanced, if_neg hne]

/-- The unmatched-couple cancellation used in a finite tree expansion.  It
is exact and makes no independence assumption beyond Haar initial phases. -/
theorem integral_binaryTreeCoupleCharacter_eq_zero_of_unmatched
    {Mode : Type*} [Fintype Mode] [DecidableEq Mode]
    (couple : BinaryInteractionTreeCouple Mode)
    (hunmatched : ¬ leafPhaseBalanced couple) :
    (∫ phase : UnitAddTorus Mode,
      binaryTreeCoupleCharacter couple phase ∂finitePhaseHaarLaw Mode) = 0 := by
  rw [integral_binaryTreeCoupleCharacter_eq_ite]
  simp [hunmatched]

/-- Coefficient-weighted form of the exact ordered-couple selector. -/
theorem integral_weightedBinaryTreeCouple_eq_ite
    {Mode : Type*} [Fintype Mode] [DecidableEq Mode]
    (kernel : BinaryTreeCoefficientKernel Mode)
    (couple : BinaryInteractionTreeCouple Mode) :
    (∫ phase : UnitAddTorus Mode,
      (binaryTreeCoefficient kernel couple.1 *
          binaryTreeCharacter couple.1 phase) *
        starRingEnd Complex
          (binaryTreeCoefficient kernel couple.2 *
            binaryTreeCharacter couple.2 phase)
      ∂finitePhaseHaarLaw Mode) =
      if leafPhaseBalanced couple then
        binaryTreeCoefficient kernel couple.1 *
          starRingEnd Complex (binaryTreeCoefficient kernel couple.2)
      else 0 := by
  simp only [map_mul]
  have hfactor :
      (fun phase : UnitAddTorus Mode ↦
        (binaryTreeCoefficient kernel couple.1 *
            binaryTreeCharacter couple.1 phase) *
          (starRingEnd Complex (binaryTreeCoefficient kernel couple.2) *
            starRingEnd Complex (binaryTreeCharacter couple.2 phase))) =
        fun phase ↦
          (binaryTreeCoefficient kernel couple.1 *
            starRingEnd Complex (binaryTreeCoefficient kernel couple.2)) *
            binaryTreeCoupleCharacter couple phase := by
    funext phase
    unfold binaryTreeCoupleCharacter
    ring
  rw [hfactor, integral_const_mul,
    integral_binaryTreeCoupleCharacter_eq_ite]
  split_ifs <;> simp

theorem integral_weightedBinaryTreeCouple_eq_zero_of_unmatched
    {Mode : Type*} [Fintype Mode] [DecidableEq Mode]
    (kernel : BinaryTreeCoefficientKernel Mode)
    (couple : BinaryInteractionTreeCouple Mode)
    (hunmatched : ¬ leafPhaseBalanced couple) :
    (∫ phase : UnitAddTorus Mode,
      (binaryTreeCoefficient kernel couple.1 *
          binaryTreeCharacter couple.1 phase) *
        starRingEnd Complex
          (binaryTreeCoefficient kernel couple.2 *
            binaryTreeCharacter couple.2 phase)
      ∂finitePhaseHaarLaw Mode) = 0 := by
  rw [integral_weightedBinaryTreeCouple_eq_ite]
  simp [hunmatched]

/-! ## Exact low-order adapters to the physical Picard indexing -/

theorem phaseSignActCharge_phaseLeaf_eq_binarySignedModeCharge
    {Mode : Type*} [DecidableEq Mode]
    (mode : Mode) (sign : Fin 2) :
    phaseSignActCharge (binaryPhaseSign sign)
        (SignedMode.mk mode .phase).charge =
      (binarySignedMode mode sign).charge := by
  fin_cases sign <;>
    ext test <;>
    simp [phaseSignActCharge, binarySignedMode, SignedMode.charge,
      Pi.single_apply]

@[simp] theorem neg_phaseSignedModeCharge_eq_conjugateSignedModeCharge
    {Mode : Type*} [DecidableEq Mode] (mode : Mode) :
    -(SignedMode.mk mode .phase).charge =
      (SignedMode.mk mode .conjugate).charge := by
  ext test
  by_cases htest : test = mode <;>
    simp [SignedMode.charge, Pi.single_apply, htest]

@[simp] theorem negOne_smul_phaseSignedModeCharge_eq_conjugateSignedModeCharge
    {Mode : Type*} [DecidableEq Mode] (mode : Mode) :
    (-1 : Int) • (SignedMode.mk mode .phase).charge =
      (SignedMode.mk mode .conjugate).charge := by
  rw [neg_one_smul]
  exact neg_phaseSignedModeCharge_eq_conjugateSignedModeCharge mode

theorem phaseSignActReal_binaryPhaseSign
    (sign : Fin 2) (value : Real) :
    phaseSignActReal (binaryPhaseSign sign) value =
      firstPicardCoordinateBranchSign sign * value := by
  fin_cases sign <;>
    simp [phaseSignActReal, firstPicardCoordinateBranchSign]

theorem chargeFrequency_binarySignedMode
    {Mode : Type*} [Fintype Mode] [DecidableEq Mode]
    (frequency : Mode → Real) (mode : Mode) (sign : Fin 2) :
    chargeFrequency (binarySignedMode mode sign).charge frequency =
      phaseSignActReal (binaryPhaseSign sign) (frequency mode) := by
  fin_cases sign <;>
    simp [chargeFrequency, binarySignedMode, SignedMode.charge,
      phaseSignActReal, Pi.single_apply]

/-- The one-vertex tree attached to an existing signed quadratic term. -/
def quadraticPhaseBinaryTree
    {N : Nat} [NeZero N] (observed : Lattice.Site N)
    (term : QuadraticPhaseTerm N) :
    RandomEigenmodeBinaryTree (Lattice.Site N) :=
  .node observed
    (binaryPhaseSign term.2.1) (binaryPhaseSign term.2.2)
    (.leaf (term.1 0)) (.leaf (term.1 1))

@[simp] theorem quadraticPhaseBinaryTree_order
    {N : Nat} [NeZero N] (observed : Lattice.Site N)
    (term : QuadraticPhaseTerm N) :
    (quadraticPhaseBinaryTree observed term).shape.order = 1 := rfl

theorem binaryTreePhaseCharge_quadraticPhaseBinaryTree
    {N : Nat} [NeZero N] (observed : Lattice.Site N)
    (term : QuadraticPhaseTerm N) :
    binaryTreePhaseCharge (quadraticPhaseBinaryTree observed term) =
      quadraticPhaseCharge term := by
  unfold quadraticPhaseBinaryTree quadraticPhaseCharge
  simp only [binaryTreePhaseCharge_node, binaryTreePhaseCharge_leaf,
    phaseSignActCharge_phaseLeaf_eq_binarySignedModeCharge]

/-- The recursive tree mismatch is exactly the already verified first-Picard
quadratic mismatch. -/
theorem binaryTreeFrequencyMismatch_quadraticPhaseBinaryTree
    {N : Nat} [NeZero N]
    (frequency : Lattice.Site N → Real) (observed : Lattice.Site N)
    (term : QuadraticPhaseTerm N) :
    binaryTreeFrequencyMismatch frequency
        (quadraticPhaseBinaryTree observed term) =
      quadraticPhaseMismatch frequency observed term := by
  rw [binaryTreeFrequencyMismatch, quadraticPhaseMismatch_eq_output_sub_chargeFrequency,
    binaryTreeCarriedFrequency_eq_chargeFrequency,
    binaryTreePhaseCharge_quadraticPhaseBinaryTree]
  rfl

theorem phaseSignActCharge_quadraticPhaseCharge_eq_coordinateCharge
    {N : Nat} [NeZero N]
    (entry : QuadraticFirstPicardCoordinateCharacterTerm N) :
    phaseSignActCharge (binaryPhaseSign entry.2)
        (quadraticPhaseCharge entry.1) =
      physlibQuadraticFirstPicardCoordinateCharacterCharge entry := by
  rcases entry with ⟨innerTerm, branch⟩
  fin_cases branch <;>
    simp [physlibQuadraticFirstPicardCoordinateCharacterCharge]

/-- The two-vertex tree corresponding to one term of the exact P3
iterated-quadratic character family.  The first-Picard child is inserted in
the recorded outer tensor slot. -/
def iteratedQuadraticSecondPicardBinaryTree
    {N : Nat} [NeZero N] (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N) :
    RandomEigenmodeBinaryTree (Lattice.Site N) :=
  let inner := quadraticPhaseBinaryTree
    (iteratedQuadraticFirstPicardMode term)
    (iteratedQuadraticInnerEntry term).1
  let free := RandomEigenmodeBinaryTree.leaf
    (iteratedQuadraticFreeMode term)
  let innerSign := binaryPhaseSign (iteratedQuadraticInnerEntry term).2
  let freeSign := binaryPhaseSign (iteratedQuadraticFreeSign term)
  if iteratedQuadraticFirstPicardSlot term = 0 then
    .node observed innerSign freeSign inner free
  else
    .node observed freeSign innerSign free inner

theorem iteratedQuadraticSecondPicardBinaryTree_order
    {N : Nat} [NeZero N] (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N) :
    (iteratedQuadraticSecondPicardBinaryTree observed term).shape.order = 2 := by
  rcases term with ⟨outerModes, firstSlot, freeSign, innerTerm, innerBranch⟩
  fin_cases firstSlot <;>
    rfl

/-- The generic recursive leaf charge is exactly the charge used by the
actual second-Picard character expansion. -/
theorem binaryTreePhaseCharge_iteratedQuadraticSecondPicardBinaryTree
    {N : Nat} [NeZero N] (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N) :
    binaryTreePhaseCharge
        (iteratedQuadraticSecondPicardBinaryTree observed term) =
      iteratedQuadraticSecondPicardCharge term := by
  rcases term with ⟨outerModes, firstSlot, freeSign, innerTerm, innerBranch⟩
  fin_cases firstSlot <;> fin_cases freeSign <;> fin_cases innerBranch <;>
    simp [iteratedQuadraticSecondPicardBinaryTree,
      iteratedQuadraticSecondPicardCharge, iteratedQuadraticFreeCharge,
      iteratedQuadraticFirstPicardMode, iteratedQuadraticFreeMode,
      iteratedQuadraticFirstPicardSlot, iteratedQuadraticFreeSign,
      iteratedQuadraticInnerEntry, iteratedQuadraticOuterModes,
      quadraticPhaseBinaryTree,
      phaseSignActCharge_phaseLeaf_eq_binarySignedModeCharge,
      quadraticPhaseCharge, binarySignedMode, add_comm]

/-- The mismatch of the inner node, after applying the coordinate branch,
is exactly the established inner mismatch of the physical P3 term. -/
theorem signedInnerTreeMismatch_eq_iteratedQuadraticInnerMismatch
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N) :
    phaseSignActReal (binaryPhaseSign (iteratedQuadraticInnerEntry term).2)
        (binaryTreeFrequencyMismatch (modeFrequency m)
          (quadraticPhaseBinaryTree
            (iteratedQuadraticFirstPicardMode term)
            (iteratedQuadraticInnerEntry term).1)) =
      iteratedQuadraticInnerMismatch m term := by
  rw [binaryTreeFrequencyMismatch_quadraticPhaseBinaryTree,
    phaseSignActReal_binaryPhaseSign]
  rfl

/-- The local root mismatch is the already established outer mismatch of
the physical two-vertex P3 tree. -/
theorem rootVertexMismatch_eq_iteratedQuadraticOuterMismatch
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N) :
    let innerMode := iteratedQuadraticFirstPicardMode term
    let freeMode := iteratedQuadraticFreeMode term
    let innerSign := binaryPhaseSign (iteratedQuadraticInnerEntry term).2
    let freeSign := binaryPhaseSign (iteratedQuadraticFreeSign term)
    (if iteratedQuadraticFirstPicardSlot term = 0 then
      binaryVertexMismatch (modeFrequency m) observed
        innerSign freeSign innerMode freeMode
    else
      binaryVertexMismatch (modeFrequency m) observed
        freeSign innerSign freeMode innerMode) =
      iteratedQuadraticOuterMismatch m observed term := by
  rcases term with ⟨outerModes, firstSlot, freeSign, innerTerm, innerBranch⟩
  fin_cases firstSlot <;> fin_cases freeSign <;> fin_cases innerBranch <;>
    simp [binaryVertexMismatch, phaseSignActReal,
      iteratedQuadraticOuterMismatch, iteratedQuadraticFreeCharge,
      iteratedQuadraticFirstPicardMode, iteratedQuadraticFreeMode,
      iteratedQuadraticFirstPicardSlot, iteratedQuadraticFreeSign,
      iteratedQuadraticInnerEntry, iteratedQuadraticOuterModes,
      chargeFrequency_binarySignedMode,
      firstPicardCoordinateBranchSign] <;>
    ring

end

end ArchonPhysics.PhyslibFPUTBinaryInteractionTreeCouples
