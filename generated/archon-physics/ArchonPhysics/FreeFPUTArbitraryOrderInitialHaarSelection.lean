import ArchonPhysics.FreeFPUTBinaryTreeCatalanMomentumCounting

/-!
# Arbitrary-order initial Haar selection for free FPUT histories

Every finite Picard/Duhamel term of the cubic-leading FPUT chain is a rooted
binary tree whose terminal leaves are initial modal amplitudes or their
complex conjugates.  This file connects that arbitrary-order tree language
to the exact product-Haar character algebra already proved in
`FinitePhaseMonomials` and `PhyslibFPUTBinaryInteractionTreeCouples`.

The result is an exact finite-volume selection rule at the initial time:

* a signed monomial has nonzero Haar expectation only when, at every mode,
  the number of phase leaves equals the number of conjugate-phase leaves;
* an arbitrary finite signed forest of interaction trees obeys the same
  all-mode balance rule;
* the rule applies directly to the existing `FixedRootRawHistoryIndex` at
  every finite perturbative order, after the canonical momentum completion;
* unmatched raw history couples have exactly zero initial Haar cross moment.

This is a high-order **initial-data** selection rule.  It does not assert
positive-time RPA, propagation of chaos, decay of nonlinear connected
cumulants, or the `g⁻²` recollision estimate needed for the kinetic limit.
-/

namespace ArchonPhysics.FreeFPUTArbitraryOrderInitialHaarSelection

open MeasureTheory
open UnitAddTorus
open ArchonPhysics
open ArchonPhysics.FinitePhaseMonomials
open ArchonPhysics.FreeFPUTBinaryTreeCatalanMomentumCounting
open ArchonPhysics.FreeFPUTBinaryTreeMomentumFiberCounting
open ArchonPhysics.Lattice
open ArchonPhysics.PhyslibFPUTBinaryInteractionTreeCouples
open ArchonPhysics.RandomPhaseMoments

noncomputable section

/-! ## Signed occurrence counts -/

variable {Mode : Type*} [Fintype Mode] [DecidableEq Mode]

/-- Number of unconjugated occurrences of one mode in a signed monomial. -/
def phaseMultiplicity (factors : List (SignedMode Mode)) (mode : Mode) : Nat :=
  match factors with
  | [] => 0
  | factor :: rest =>
      (if factor.mode = mode ∧ factor.sign = .phase then 1 else 0) +
        phaseMultiplicity rest mode

/-- Number of conjugated occurrences of one mode in a signed monomial. -/
def conjugateMultiplicity
    (factors : List (SignedMode Mode)) (mode : Mode) : Nat :=
  match factors with
  | [] => 0
  | factor :: rest =>
      (if factor.mode = mode ∧ factor.sign = .conjugate then 1 else 0) +
        conjugateMultiplicity rest mode

omit [Fintype Mode] in
/-- The integer charge at one mode is exactly the difference between its
unconjugated and conjugated occurrence counts.  Repeated leaves are counted
with their full multiplicity. -/
theorem monomialCharge_apply_eq_multiplicity_sub
    (factors : List (SignedMode Mode)) (mode : Mode) :
    monomialCharge factors mode =
      (phaseMultiplicity factors mode : Int) -
        (conjugateMultiplicity factors mode : Int) := by
  induction factors with
  | nil => simp [monomialCharge, phaseMultiplicity, conjugateMultiplicity]
  | cons factor rest ih =>
      rcases factor with ⟨factorMode, sign⟩
      cases sign <;> by_cases hmode : factorMode = mode <;>
        simp [monomialCharge, SignedMode.charge,
          phaseMultiplicity, conjugateMultiplicity, ih, hmode,
          eq_comm] <;> ring

omit [Fintype Mode] in
/-- Zero total charge is equivalent to equality of positive and negative
leaf multiplicities separately at every mode. -/
theorem monomialCharge_eq_zero_iff_multiplicity_balanced
    (factors : List (SignedMode Mode)) :
    monomialCharge factors = 0 ↔
      ∀ mode, phaseMultiplicity factors mode =
        conjugateMultiplicity factors mode := by
  constructor
  · intro hcharge mode
    have hmode := congrFun hcharge mode
    rw [monomialCharge_apply_eq_multiplicity_sub] at hmode
    simp only [Pi.zero_apply, sub_eq_zero] at hmode
    exact_mod_cast hmode
  · intro hbalanced
    funext mode
    rw [monomialCharge_apply_eq_multiplicity_sub]
    simp [hbalanced mode]

/-- Wick-like selection rule for arbitrary finite signed Haar monomials.
Unlike Gaussian Wick expansion, the selector is only charge balance: when it
holds the unit-character expectation is one, and otherwise it is zero. -/
theorem integral_unitSignedMonomial_eq_multiplicitySelector
    (factors : List (SignedMode Mode)) :
    (∫ phase : UnitAddTorus Mode, unitSignedMonomial factors phase
      ∂finitePhaseHaarLaw Mode) =
      if (∀ mode, phaseMultiplicity factors mode =
          conjugateMultiplicity factors mode) then 1 else 0 := by
  rw [integral_unitSignedMonomial_eq_ite]
  exact if_congr (monomialCharge_eq_zero_iff_multiplicity_balanced factors) rfl rfl

/-- A single mode with unequal phase/conjugate multiplicities annihilates
the entire arbitrary-degree monomial exactly. -/
theorem integral_unitSignedMonomial_eq_zero_of_unbalancedMode
    (factors : List (SignedMode Mode)) (mode : Mode)
    (hunbalanced : phaseMultiplicity factors mode ≠
      conjugateMultiplicity factors mode) :
    (∫ phase : UnitAddTorus Mode, unitSignedMonomial factors phase
      ∂finitePhaseHaarLaw Mode) = 0 := by
  rw [integral_unitSignedMonomial_eq_multiplicitySelector]
  rw [if_neg]
  intro hbalanced
  exact hunbalanced (hbalanced mode)

omit [DecidableEq Mode] in
/-- A bare three-wave phase monomial with signs `(+,+,-)` always has zero
initial Haar expectation.  This is a concrete triad instance of the
all-mode rule, not a statement about a nonlinear triad at positive time. -/
theorem integral_phase_phase_conjugate_triad_eq_zero
    (first second third : Mode) :
    (∫ phase : UnitAddTorus Mode,
      unitSignedMonomial
        [⟨first, .phase⟩, ⟨second, .phase⟩, ⟨third, .conjugate⟩]
        phase ∂finitePhaseHaarLaw Mode) = 0 := by
  classical
  by_cases hfirstThird : first = third
  · subst third
    by_cases hfirstSecond : first = second
    · subst second
      apply integral_unitSignedMonomial_eq_zero_of_unbalancedMode _ first
      simp [phaseMultiplicity, conjugateMultiplicity]
    · apply integral_unitSignedMonomial_eq_zero_of_unbalancedMode _ second
      simp [phaseMultiplicity, conjugateMultiplicity, hfirstSecond]
  · by_cases hfirstSecond : first = second
    · subst second
      apply integral_unitSignedMonomial_eq_zero_of_unbalancedMode _ first
      simp [phaseMultiplicity, conjugateMultiplicity, Ne.symm hfirstThird]
    · apply integral_unitSignedMonomial_eq_zero_of_unbalancedMode _ first
      simp [phaseMultiplicity, conjugateMultiplicity,
        Ne.symm hfirstThird, Ne.symm hfirstSecond]

/-! ## Arbitrary signed forests of binary interaction histories -/

/-- One Duhamel tree together with the outer choice of the term or its
complex conjugate in a higher moment. -/
abbrev SignedInteractionTree (Mode : Type*) :=
  PhaseSign × RandomEigenmodeBinaryTree Mode

/-- Literal initial leaves of an arbitrary finite signed forest.  Applying
the outer sign flips every descendant leaf sign, exactly as conjugating the
whole Duhamel term does. -/
def signedInteractionForestLeaves
    (forest : List (SignedInteractionTree Mode)) : List (SignedMode Mode) :=
  forest.flatMap fun entry =>
    (binaryTreeSignedLeaves entry.2).map
      (phaseSignActSignedMode entry.1)

/-- Complete initial phase charge of a finite interaction forest. -/
def signedInteractionForestCharge
    (forest : List (SignedInteractionTree Mode)) : Mode → Int :=
  monomialCharge (signedInteractionForestLeaves forest)

/-- The flattened-leaf charge is the recursive signed sum of the charges of
all constituent Duhamel trees. -/
theorem signedInteractionForestCharge_cons
    (entry : SignedInteractionTree Mode)
    (forest : List (SignedInteractionTree Mode)) :
    signedInteractionForestCharge (entry :: forest) =
      phaseSignActCharge entry.1 (binaryTreePhaseCharge entry.2) +
        signedInteractionForestCharge forest := by
  unfold signedInteractionForestCharge signedInteractionForestLeaves
  rw [List.flatMap_cons, monomialCharge_append,
    monomialCharge_map_phaseSignActSignedMode,
    monomialCharge_binaryTreeSignedLeaves]

/-- Initial phase monomial carried by a finite interaction forest. -/
def signedInteractionForestMonomial
    (forest : List (SignedInteractionTree Mode))
    (phase : UnitAddTorus Mode) : Complex :=
  unitSignedMonomial (signedInteractionForestLeaves forest) phase

/-- Recursive-tree form of the arbitrary-order initial Haar selector. -/
theorem integral_signedInteractionForestMonomial_eq_ite
    (forest : List (SignedInteractionTree Mode)) :
    (∫ phase : UnitAddTorus Mode,
      signedInteractionForestMonomial forest phase
      ∂finitePhaseHaarLaw Mode) =
      if signedInteractionForestCharge forest = 0 then 1 else 0 := by
  change
    (∫ phase : UnitAddTorus Mode,
      unitSignedMonomial (signedInteractionForestLeaves forest) phase
      ∂finitePhaseHaarLaw Mode) =
      if monomialCharge (signedInteractionForestLeaves forest) = 0
      then 1 else 0
  exact integral_unitSignedMonomial_eq_ite
    (signedInteractionForestLeaves forest)

/-- Any explicitly exhibited unbalanced mode kills a forest expectation.
This applies to triads and to every higher Duhamel moment without imposing a
positive-time independence hypothesis. -/
theorem integral_signedInteractionForestMonomial_eq_zero_of_unbalancedMode
    (forest : List (SignedInteractionTree Mode)) (mode : Mode)
    (hunbalanced : signedInteractionForestCharge forest mode ≠ 0) :
    (∫ phase : UnitAddTorus Mode,
      signedInteractionForestMonomial forest phase
      ∂finitePhaseHaarLaw Mode) = 0 := by
  rw [integral_signedInteractionForestMonomial_eq_ite]
  rw [if_neg]
  intro hzero
  exact hunbalanced (congrFun hzero mode)

/-! ## Canonical adapter from fixed-root raw FPUT histories -/

/-- Convert a signed momentum tree with its complete internal momentum
decoration into the decorated tree used by the Physlib FPUT coefficient and
Haar-couple APIs. -/
def realizedEigenmodeTree {N : Nat} :
    (tree : SignedMomentumBinaryTree) →
      tree.FullMomentumDecoration N →
        RandomEigenmodeBinaryTree (Site N)
  | .leaf, momentum => .leaf momentum
  | .node leftSign rightSign left right, decoration =>
      .node decoration.1 leftSign rightSign
        (realizedEigenmodeTree left decoration.2.1)
        (realizedEigenmodeTree right decoration.2.2)

/-- Realization preserves the complete signed binary shape. -/
@[simp] theorem shape_realizedEigenmodeTree {N : Nat}
    (tree : SignedMomentumBinaryTree)
    (decoration : tree.FullMomentumDecoration N) :
    (realizedEigenmodeTree tree decoration).shape = tree.shape := by
  induction tree with
  | leaf => rfl
  | node leftSign rightSign left right hleft hright =>
      rcases decoration with ⟨root, leftDecoration, rightDecoration⟩
      simp [realizedEigenmodeTree, RandomEigenmodeBinaryTree.shape,
        SignedMomentumBinaryTree.shape, hleft, hright]

/-- Canonical realization of one existing fixed-root arbitrary-order raw
history: its leaf momenta uniquely complete all internal momenta. -/
def realizeFixedRootRawHistory
    {N r : Nat} [NeZero N] (rootMomentum : Site N)
    (history : FixedRootRawHistoryIndex N r rootMomentum) :
    RandomEigenmodeBinaryTree (Site N) :=
  let signedTree :=
    signedMomentumTreeOfDecoration history.1.1 history.2.1
  realizedEigenmodeTree signedTree
    (signedTree.completeMomentumDecoration history.2.2.1)

/-- The canonical realization has exactly the perturbative order recorded
by the raw-history index. -/
@[simp] theorem realizeFixedRootRawHistory_shape_order
    {N r : Nat} [NeZero N] (rootMomentum : Site N)
    (history : FixedRootRawHistoryIndex N r rootMomentum) :
    (realizeFixedRootRawHistory rootMomentum history).shape.order = r := by
  rw [realizeFixedRootRawHistory, shape_realizedEigenmodeTree,
    shape_signedMomentumTreeOfDecoration]
  exact history.1.2

/-- A signed list of existing raw histories, all at one arbitrary finite
order and fixed output momentum. -/
def realizeFixedRootRawHistoryForest
    {N r : Nat} [NeZero N] (rootMomentum : Site N)
    (forest : List (PhaseSign ×
      FixedRootRawHistoryIndex N r rootMomentum)) :
    List (SignedInteractionTree (Site N)) :=
  forest.map fun entry =>
    (entry.1, realizeFixedRootRawHistory rootMomentum entry.2)

/-- Initial character carried by an arbitrary high-order fixed-root raw
history forest. -/
def fixedRootRawHistoryForestMonomial
    {N r : Nat} [NeZero N] (rootMomentum : Site N)
    (forest : List (PhaseSign ×
      FixedRootRawHistoryIndex N r rootMomentum))
    (phase : UnitAddTorus (Site N)) : Complex :=
  signedInteractionForestMonomial
    (realizeFixedRootRawHistoryForest rootMomentum forest) phase

/-- Complete leaf charge of an arbitrary high-order fixed-root raw history
forest. -/
def fixedRootRawHistoryForestCharge
    {N r : Nat} [NeZero N] (rootMomentum : Site N)
    (forest : List (PhaseSign ×
      FixedRootRawHistoryIndex N r rootMomentum)) : Site N → Int :=
  signedInteractionForestCharge
    (realizeFixedRootRawHistoryForest rootMomentum forest)

/-- Exact all-order initial Haar selector on the actual fixed-root raw FPUT
history index used by the Catalan/Duhamel expansion. -/
theorem integral_fixedRootRawHistoryForestMonomial_eq_ite
    {N r : Nat} [NeZero N] (rootMomentum : Site N)
    (forest : List (PhaseSign ×
      FixedRootRawHistoryIndex N r rootMomentum)) :
    (∫ phase : UnitAddTorus (Site N),
      fixedRootRawHistoryForestMonomial rootMomentum forest phase
      ∂finitePhaseHaarLaw (Site N)) =
      if fixedRootRawHistoryForestCharge rootMomentum forest = 0
      then 1 else 0 := by
  exact integral_signedInteractionForestMonomial_eq_ite
    (realizeFixedRootRawHistoryForest rootMomentum forest)

/-- The same arbitrary-order selector for the actual finite phase block of
any verified iid mass/phase ensemble.  Only the initial `restrictPhase` law
is used; the masses and all later Hamiltonian evolution are untouched. -/
theorem ensemble_fixedRootRawHistoryForestMonomial_expectation
    {Omega : Type*} [MeasurableSpace Omega]
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N r : Nat} [NeZero N] (rootMomentum : Site N)
    (forest : List (PhaseSign ×
      FixedRootRawHistoryIndex N r rootMomentum)) :
    (∫ omega,
      fixedRootRawHistoryForestMonomial rootMomentum forest
        (ensemble.restrictPhase omega)
      ∂ensemble.probability) =
      if fixedRootRawHistoryForestCharge rootMomentum forest = 0
      then 1 else 0 := by
  change
    (∫ omega,
      unitSignedMonomial
          (signedInteractionForestLeaves
            (realizeFixedRootRawHistoryForest rootMomentum forest))
          (ensemble.restrictPhase omega)
      ∂ensemble.probability) =
      if monomialCharge
          (signedInteractionForestLeaves
            (realizeFixedRootRawHistoryForest rootMomentum forest)) = 0
      then 1 else 0
  exact ensemble_unitSignedMonomial_expectation ensemble
    (signedInteractionForestLeaves
      (realizeFixedRootRawHistoryForest rootMomentum forest))

/-- A concrete all-order cancellation certificate: finding just one mode
whose signed leaf count is nonzero proves exact vanishing of the initial
Haar expectation. -/
theorem integral_fixedRootRawHistoryForestMonomial_eq_zero_of_unbalancedMode
    {N r : Nat} [NeZero N] (rootMomentum mode : Site N)
    (forest : List (PhaseSign ×
      FixedRootRawHistoryIndex N r rootMomentum))
    (hunbalanced :
      fixedRootRawHistoryForestCharge rootMomentum forest mode ≠ 0) :
    (∫ phase : UnitAddTorus (Site N),
      fixedRootRawHistoryForestMonomial rootMomentum forest phase
      ∂finitePhaseHaarLaw (Site N)) = 0 := by
  exact integral_signedInteractionForestMonomial_eq_zero_of_unbalancedMode
    (realizeFixedRootRawHistoryForest rootMomentum forest) mode hunbalanced

/-- Character of an existing raw tree couple after canonical realization. -/
def fixedRootRawHistoryCoupleCharacter
    {N r : Nat} [NeZero N] (rootMomentum : Site N)
    (couple : FixedRootRawCoupleIndex N r rootMomentum)
    (phase : UnitAddTorus (Site N)) : Complex :=
  binaryTreeCoupleCharacter
    (realizeFixedRootRawHistory rootMomentum couple.1,
      realizeFixedRootRawHistory rootMomentum couple.2) phase

/-- Exact second-moment selector for arbitrary-order raw FPUT couples. -/
theorem integral_fixedRootRawHistoryCoupleCharacter_eq_ite
    {N r : Nat} [NeZero N] (rootMomentum : Site N)
    (couple : FixedRootRawCoupleIndex N r rootMomentum) :
    (∫ phase : UnitAddTorus (Site N),
      fixedRootRawHistoryCoupleCharacter rootMomentum couple phase
      ∂finitePhaseHaarLaw (Site N)) =
      if leafPhaseBalanced
          (realizeFixedRootRawHistory rootMomentum couple.1,
            realizeFixedRootRawHistory rootMomentum couple.2)
      then 1 else 0 := by
  exact integral_binaryTreeCoupleCharacter_eq_ite
    (realizeFixedRootRawHistory rootMomentum couple.1,
      realizeFixedRootRawHistory rootMomentum couple.2)

/-- If two arbitrary-order raw histories disagree in their total leaf charge
at one mode, their initial Haar cross moment is exactly zero. -/
theorem integral_fixedRootRawHistoryCoupleCharacter_eq_zero_of_charge_ne
    {N r : Nat} [NeZero N] (rootMomentum mode : Site N)
    (couple : FixedRootRawCoupleIndex N r rootMomentum)
    (hunmatched :
      binaryTreePhaseCharge
          (realizeFixedRootRawHistory rootMomentum couple.1) mode ≠
        binaryTreePhaseCharge
          (realizeFixedRootRawHistory rootMomentum couple.2) mode) :
    (∫ phase : UnitAddTorus (Site N),
      fixedRootRawHistoryCoupleCharacter rootMomentum couple phase
      ∂finitePhaseHaarLaw (Site N)) = 0 := by
  unfold fixedRootRawHistoryCoupleCharacter
  apply integral_binaryTreeCoupleCharacter_eq_zero_of_unmatched
  intro hbalanced
  exact hunmatched (hbalanced mode)

end

end ArchonPhysics.FreeFPUTArbitraryOrderInitialHaarSelection
