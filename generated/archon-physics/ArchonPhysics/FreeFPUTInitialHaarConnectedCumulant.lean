import ArchonPhysics.FreeFPUTArbitraryOrderInitialHaarSelection
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Order.Partition.Finpartition

/-!
# Connected cumulants of initial Haar FPUT histories

This module upgrades the arbitrary-order initial character selector from a
single monomial expectation to the finite joint-cumulant algebra used by a
Duhamel diagram expansion.

For a finite nonempty index type `I`, the connected cumulant supplied by
block moments `M(B)` is defined by the standard partition/Möbius formula

`sum_pi (-1)^(|pi|-1) (|pi|-1)! * product_(B in pi) M(B)`.

Each indexed signed FPUT tree carries its exact initial phase-charge vector.
The charge of a block is the sum of the charges of its members.  Mathlib's
`Finpartition` API then proves that the sum of all block charges in any
partition is the total charge.  Hence, if the total charge is nonzero, every
partition has at least one nonzero-charge block.  Product Haar annihilates
that block moment, so every partition term -- and therefore the connected
cumulant -- is exactly zero.

The final section specializes this statement to the existing arbitrary-order
`FixedRootRawHistoryIndex` and to the actual finite phase restriction of any
verified `IIDMassPhaseEnsemble`.

All results concern the initial iid Haar law.  They do not assert nonlinear
positive-time propagation of chaos, decay of connected cumulants, or the
`g⁻²` recollision estimate required for Hamiltonian-to-kinetic convergence.
-/

namespace ArchonPhysics.FreeFPUTInitialHaarConnectedCumulant

open MeasureTheory
open UnitAddTorus
open ArchonPhysics
open ArchonPhysics.FiniteEnsemblePhaseMoments
open ArchonPhysics.FinitePhaseMonomials
open ArchonPhysics.FreeFPUTArbitraryOrderInitialHaarSelection
open ArchonPhysics.FreeFPUTBinaryTreeCatalanMomentumCounting
open ArchonPhysics.Lattice
open ArchonPhysics.PhyslibFPUTBinaryInteractionTreeCouples
open ArchonPhysics.RandomPhaseMoments

noncomputable section

/-! ## Abstract finite joint cumulant -/

/-- Möbius coefficient of one set partition in the joint-cumulant formula. -/
def partitionMobiusCoefficient
    {I : Type*} [Fintype I] [DecidableEq I]
    (partition : Finpartition (Finset.univ : Finset I)) : Complex :=
  (-1 : Complex) ^ (partition.parts.card - 1) *
    (Nat.factorial (partition.parts.card - 1) : Complex)

/-- Joint cumulant reconstructed from supplied moments of every finite block.
The index type is nonempty, as in the usual positive-order cumulant. -/
def suppliedJointCumulant
    {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    (blockMoment : Finset I → Complex) : Complex :=
  ∑ partition : Finpartition (Finset.univ : Finset I),
    partitionMobiusCoefficient partition *
      ∏ block ∈ partition.parts, blockMoment block

/-! ## Charges and block characters of indexed interaction trees -/

variable {Mode I : Type*}
  [Fintype Mode] [DecidableEq Mode]
  [Fintype I] [DecidableEq I] [Nonempty I]

/-- Initial charge of one Duhamel tree, including the outer choice of the
term or its complex conjugate in the joint moment. -/
def signedInteractionTreeCharge
    (entry : SignedInteractionTree Mode) : Mode → Int :=
  phaseSignActCharge entry.1 (binaryTreePhaseCharge entry.2)

/-- Total charge of the entries belonging to one partition block. -/
def indexedSignedTreeBlockCharge
    (entry : I → SignedInteractionTree Mode) (block : Finset I) :
    Mode → Int :=
  ∑ i ∈ block, signedInteractionTreeCharge (entry i)

/-- Charge of the complete indexed forest. -/
def indexedSignedTreeTotalCharge
    (entry : I → SignedInteractionTree Mode) : Mode → Int :=
  ∑ i, signedInteractionTreeCharge (entry i)

/-- Initial character of the product of all signed tree monomials in a
partition block. -/
def indexedSignedTreeBlockMonomial
    (entry : I → SignedInteractionTree Mode) (block : Finset I)
    (phase : UnitAddTorus Mode) : Complex :=
  mFourier (indexedSignedTreeBlockCharge entry block) phase

omit [Fintype I] [DecidableEq I] [Nonempty I] in
/-- The block character is literally the product of its individual signed
tree characters. -/
theorem indexedSignedTreeBlockMonomial_eq_prod
    (entry : I → SignedInteractionTree Mode) (block : Finset I)
    (phase : UnitAddTorus Mode) :
    indexedSignedTreeBlockMonomial entry block phase =
      ∏ i ∈ block,
        mFourier (signedInteractionTreeCharge (entry i)) phase := by
  classical
  induction block using Finset.induction with
  | empty =>
      simp [indexedSignedTreeBlockMonomial,
        indexedSignedTreeBlockCharge, mFourier_zero]
  | @insert index block hindex ih =>
      unfold indexedSignedTreeBlockMonomial at ih ⊢
      rw [show indexedSignedTreeBlockCharge entry (insert index block) =
          signedInteractionTreeCharge (entry index) +
            indexedSignedTreeBlockCharge entry block by
        simp [indexedSignedTreeBlockCharge, hindex]]
      rw [mFourier_add, Finset.prod_insert hindex, ih]

/-- Exact product-Haar block moment selector. -/
def initialHaarSignedTreeBlockMoment
    (entry : I → SignedInteractionTree Mode) (block : Finset I) : Complex :=
  if indexedSignedTreeBlockCharge entry block = 0 then 1 else 0

omit [Fintype I] [DecidableEq I] [Nonempty I] in
/-- Product Haar evaluates a block product by its complete mode-charge. -/
theorem integral_indexedSignedTreeBlockMonomial_eq_selector
    (entry : I → SignedInteractionTree Mode) (block : Finset I) :
    (∫ phase : UnitAddTorus Mode,
      indexedSignedTreeBlockMonomial entry block phase
      ∂finitePhaseHaarLaw Mode) =
      initialHaarSignedTreeBlockMoment entry block := by
  exact integral_mFourier_eq_ite
    (indexedSignedTreeBlockCharge entry block)

/-! ## Every partition of an unbalanced forest has an unbalanced block -/

omit [Nonempty I] in
/-- Summing the charges of all blocks of a partition recovers the charge of
the complete indexed forest. -/
theorem sum_indexedSignedTreeBlockCharge_eq_total
    (entry : I → SignedInteractionTree Mode)
    (partition : Finpartition (Finset.univ : Finset I)) :
    (∑ block ∈ partition.parts,
      indexedSignedTreeBlockCharge entry block) =
      indexedSignedTreeTotalCharge entry := by
  unfold indexedSignedTreeBlockCharge indexedSignedTreeTotalCharge
  calc
    (∑ block ∈ partition.parts,
        ∑ i ∈ block, signedInteractionTreeCharge (entry i)) =
        ∑ i ∈ partition.parts.biUnion id,
          signedInteractionTreeCharge (entry i) := by
      symm
      exact Finset.sum_biUnion partition.disjoint
    _ = ∑ i, signedInteractionTreeCharge (entry i) := by
      rw [partition.biUnion_parts]

omit [Nonempty I] in
/-- If the total phase charge is unbalanced, every set partition contains at
least one unbalanced block. -/
theorem exists_unbalanced_block_of_totalCharge_ne_zero
    (entry : I → SignedInteractionTree Mode)
    (partition : Finpartition (Finset.univ : Finset I))
    (htotal : indexedSignedTreeTotalCharge entry ≠ 0) :
    ∃ block ∈ partition.parts,
      indexedSignedTreeBlockCharge entry block ≠ 0 := by
  by_contra hnone
  push Not at hnone
  apply htotal
  rw [← sum_indexedSignedTreeBlockCharge_eq_total entry partition]
  exact Finset.sum_eq_zero fun block hblock => hnone block hblock

/-! ## Initial connected-cumulant cancellation -/

/-- Connected cumulant of the exact initial Haar block selectors. -/
def initialHaarSignedTreeConnectedCumulant
    (entry : I → SignedInteractionTree Mode) : Complex :=
  suppliedJointCumulant (initialHaarSignedTreeBlockMoment entry)

omit [Nonempty I] in
/-- Every partition term in an unbalanced initial forest is exactly zero. -/
theorem initialHaar_partitionTerm_eq_zero_of_totalCharge_ne_zero
    (entry : I → SignedInteractionTree Mode)
    (partition : Finpartition (Finset.univ : Finset I))
    (htotal : indexedSignedTreeTotalCharge entry ≠ 0) :
    partitionMobiusCoefficient partition *
        (∏ block ∈ partition.parts,
          initialHaarSignedTreeBlockMoment entry block) = 0 := by
  obtain ⟨block, hblock, hunbalanced⟩ :=
    exists_unbalanced_block_of_totalCharge_ne_zero
      entry partition htotal
  have hmoment : initialHaarSignedTreeBlockMoment entry block = 0 := by
    exact if_neg hunbalanced
  rw [mul_eq_zero]
  exact Or.inr (Finset.prod_eq_zero hblock hmoment)

omit [Nonempty I] in
/-- If every block of a partition is charge-balanced, the initial Haar
selector retains that partition term exactly: no resonant block is erased.
In particular, the charge selection rule does not claim that balanced triad
or quartet contributions vanish. -/
theorem initialHaar_partitionTerm_eq_mobius_of_all_blocks_balanced
    (entry : I → SignedInteractionTree Mode)
    (partition : Finpartition (Finset.univ : Finset I))
    (hbalanced : ∀ block ∈ partition.parts,
      indexedSignedTreeBlockCharge entry block = 0) :
    partitionMobiusCoefficient partition *
        (∏ block ∈ partition.parts,
          initialHaarSignedTreeBlockMoment entry block) =
      partitionMobiusCoefficient partition := by
  have hprod :
      (∏ block ∈ partition.parts,
        initialHaarSignedTreeBlockMoment entry block) = 1 := by
    apply Finset.prod_eq_one
    intro block hblock
    exact if_pos (hbalanced block hblock)
  rw [hprod, mul_one]

/-- An initial iid Haar signed-tree forest with nonzero total mode-charge has
exactly vanishing connected cumulant, at every finite joint order and every
finite Duhamel order. -/
theorem initialHaarSignedTreeConnectedCumulant_eq_zero_of_totalCharge_ne_zero
    (entry : I → SignedInteractionTree Mode)
    (htotal : indexedSignedTreeTotalCharge entry ≠ 0) :
    initialHaarSignedTreeConnectedCumulant entry = 0 := by
  unfold initialHaarSignedTreeConnectedCumulant suppliedJointCumulant
  exact Finset.sum_eq_zero fun partition _ =>
    initialHaar_partitionTerm_eq_zero_of_totalCharge_ne_zero
      entry partition htotal

/-! ## Actual iid ensemble moments -/

/-- Actual initial block moment under the verified finite phase restriction
of an iid mass/phase ensemble. -/
def actualIIDInitialSignedTreeBlockMoment
    {Omega : Type*} [MeasurableSpace Omega]
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N]
    (entry : I → SignedInteractionTree (Lattice.Site N))
    (block : Finset I) : Complex :=
  ∫ omega,
    indexedSignedTreeBlockMonomial entry block
      (ensemble.restrictPhase omega) ∂ensemble.probability

omit [Fintype I] [DecidableEq I] [Nonempty I] in
/-- The actual iid initial block moment is exactly the Haar charge selector. -/
theorem actualIIDInitialSignedTreeBlockMoment_eq_selector
    {Omega : Type*} [MeasurableSpace Omega]
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N]
    (entry : I → SignedInteractionTree (Lattice.Site N))
    (block : Finset I) :
    actualIIDInitialSignedTreeBlockMoment ensemble entry block =
      initialHaarSignedTreeBlockMoment entry block := by
  simpa [actualIIDInitialSignedTreeBlockMoment,
    indexedSignedTreeBlockMonomial,
    initialHaarSignedTreeBlockMoment] using
      (restrictPhase_mFourier_expectation ensemble
        (indexedSignedTreeBlockCharge entry block))

/-- Connected cumulant formed from the actual iid initial block moments. -/
def actualIIDInitialSignedTreeConnectedCumulant
    {Omega : Type*} [MeasurableSpace Omega]
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N]
    (entry : I → SignedInteractionTree (Lattice.Site N)) : Complex :=
  suppliedJointCumulant
    (actualIIDInitialSignedTreeBlockMoment ensemble entry)

/-- The actual iid connected cumulant reduces exactly to the abstract Haar
selector cumulant. -/
theorem actualIIDInitialSignedTreeConnectedCumulant_eq_initialHaar
    {Omega : Type*} [MeasurableSpace Omega]
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N]
    (entry : I → SignedInteractionTree (Lattice.Site N)) :
    actualIIDInitialSignedTreeConnectedCumulant ensemble entry =
      initialHaarSignedTreeConnectedCumulant entry := by
  unfold actualIIDInitialSignedTreeConnectedCumulant
    initialHaarSignedTreeConnectedCumulant suppliedJointCumulant
  simp_rw [actualIIDInitialSignedTreeBlockMoment_eq_selector]

/-- Actual-ensemble connected-cumulant cancellation for every initially
charge-unbalanced finite tree forest. -/
theorem actualIIDInitialSignedTreeConnectedCumulant_eq_zero_of_totalCharge_ne_zero
    {Omega : Type*} [MeasurableSpace Omega]
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N]
    (entry : I → SignedInteractionTree (Lattice.Site N))
    (htotal : indexedSignedTreeTotalCharge entry ≠ 0) :
    actualIIDInitialSignedTreeConnectedCumulant ensemble entry = 0 := by
  rw [actualIIDInitialSignedTreeConnectedCumulant_eq_initialHaar]
  exact initialHaarSignedTreeConnectedCumulant_eq_zero_of_totalCharge_ne_zero
    entry htotal

/-! ## Fixed-root arbitrary-order raw-history adapter -/

/-- Canonically realized indexed forest of existing fixed-root raw histories. -/
def fixedRootIndexedRawHistoryTree
    {N r : Nat} [NeZero N] (rootMomentum : Site N)
    (history : I → PhaseSign ×
      FixedRootRawHistoryIndex N r rootMomentum) :
    I → SignedInteractionTree (Site N) :=
  fun index =>
    ((history index).1,
      realizeFixedRootRawHistory rootMomentum (history index).2)

/-- Total initial phase charge of the actual fixed-root indexed forest. -/
def fixedRootIndexedRawHistoryTotalCharge
    {N r : Nat} [NeZero N] (rootMomentum : Site N)
    (history : I → PhaseSign ×
      FixedRootRawHistoryIndex N r rootMomentum) : Site N → Int :=
  indexedSignedTreeTotalCharge
    (fixedRootIndexedRawHistoryTree rootMomentum history)

/-- Actual iid connected cumulant of a fixed-root, arbitrary-Duhamel-order
indexed raw-history forest. -/
def actualIIDFixedRootRawHistoryConnectedCumulant
    {Omega : Type*} [MeasurableSpace Omega]
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N r : Nat} [NeZero N] (rootMomentum : Site N)
    (history : I → PhaseSign ×
      FixedRootRawHistoryIndex N r rootMomentum) : Complex :=
  actualIIDInitialSignedTreeConnectedCumulant ensemble
    (fixedRootIndexedRawHistoryTree rootMomentum history)

/-- Final fixed-root statement: nonzero total initial leaf charge forces the
actual iid connected cumulant to vanish exactly. -/
theorem actualIIDFixedRootRawHistoryConnectedCumulant_eq_zero_of_totalCharge_ne_zero
    {Omega : Type*} [MeasurableSpace Omega]
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N r : Nat} [NeZero N] (rootMomentum : Site N)
    (history : I → PhaseSign ×
      FixedRootRawHistoryIndex N r rootMomentum)
    (htotal :
      fixedRootIndexedRawHistoryTotalCharge rootMomentum history ≠ 0) :
    actualIIDFixedRootRawHistoryConnectedCumulant
      ensemble rootMomentum history = 0 := by
  exact actualIIDInitialSignedTreeConnectedCumulant_eq_zero_of_totalCharge_ne_zero
    ensemble (fixedRootIndexedRawHistoryTree rootMomentum history) htotal

end

end ArchonPhysics.FreeFPUTInitialHaarConnectedCumulant
