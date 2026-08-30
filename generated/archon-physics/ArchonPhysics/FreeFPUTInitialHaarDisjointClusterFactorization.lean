import ArchonPhysics.FreeFPUTInitialHaarConnectedCumulant

/-!
# Initial Haar factorization for disjoint mode clusters

The exact initial Haar cancellation already proves that a block with nonzero
total phase charge has zero moment.  Propagation of chaos needs a second,
logically different initial statement: two collections of observables which
depend on disjoint sets of base modes have factorized joint moments, even
when the total charge of the combined collection is zero.

This module proves that statement at arbitrary finite order.  It works with
the existing signed interaction-tree characters and therefore also applies
to arbitrary finite Duhamel order.  No positive-time independence or
random-phase propagation is asserted.
-/

namespace ArchonPhysics.FreeFPUTInitialHaarDisjointClusterFactorization

open ArchonPhysics
open ArchonPhysics.FreeFPUTArbitraryOrderInitialHaarSelection
open ArchonPhysics.FreeFPUTInitialHaarConnectedCumulant
open ArchonPhysics.PhyslibFPUTBinaryInteractionTreeCouples

noncomputable section

variable {Mode I : Type*}
  [Fintype Mode] [DecidableEq Mode]
  [Fintype I] [DecidableEq I] [Nonempty I]

/-- All base modes on which at least one signed character in a finite block
depends nontrivially. -/
def indexedSignedTreeClusterModeSupport
    (entry : I → SignedInteractionTree Mode) (block : Finset I) : Set Mode :=
  {mode | ∃ i ∈ block,
    signedInteractionTreeCharge (entry i) mode ≠ 0}

omit [Nonempty I] in
/-- The support of the aggregate block charge is contained in the union of
the supports of its individual character charges. -/
theorem support_indexedSignedTreeBlockCharge_subset_clusterModeSupport
    (entry : I → SignedInteractionTree Mode) (block : Finset I) :
    Function.support (indexedSignedTreeBlockCharge entry block) ⊆
      indexedSignedTreeClusterModeSupport entry block := by
  intro mode hmode
  change indexedSignedTreeBlockCharge entry block mode ≠ 0 at hmode
  change ∃ i ∈ block,
    signedInteractionTreeCharge (entry i) mode ≠ 0
  by_contra hnone
  push Not at hnone
  apply hmode
  simp only [indexedSignedTreeBlockCharge, Finset.sum_apply]
  exact Finset.sum_eq_zero fun i hi ↦ hnone i hi

omit [Nonempty I] in
/-- Enlarging an index block can only enlarge its base-mode support. -/
theorem indexedSignedTreeClusterModeSupport_mono
    (entry : I → SignedInteractionTree Mode)
    {small large : Finset I} (hsub : small ⊆ large) :
    indexedSignedTreeClusterModeSupport entry small ⊆
      indexedSignedTreeClusterModeSupport entry large := by
  rintro mode ⟨i, hi, hcharge⟩
  exact ⟨i, hsub hi, hcharge⟩

/-- Disjoint supports prevent cancellation between two nonzero charge
functions. -/
theorem add_ne_zero_of_left_ne_zero_of_disjoint_support
    (left right : Mode → Int) (hleft : left ≠ 0)
    (hdisjoint : Disjoint (Function.support left)
      (Function.support right)) :
    left + right ≠ 0 := by
  intro hadd
  apply hleft
  funext mode
  by_contra hmode
  have hleftSupport : mode ∈ Function.support left := hmode
  have hrightNotSupport : mode ∉ Function.support right := by
    intro hrightSupport
    exact Set.disjoint_left.1 hdisjoint
      hleftSupport hrightSupport
  have hrightZero : right mode = 0 := by
    by_contra hright
    exact hrightNotSupport hright
  have hpoint := congrFun hadd mode
  change left mode + right mode = 0 at hpoint
  rw [hrightZero, add_zero] at hpoint
  exact hmode hpoint

/-- The product-Haar charge selector factorizes across disjoint charge
supports.  This includes the important case where both cluster charges
vanish and hence the combined total charge is balanced. -/
theorem haarChargeSelector_add_eq_mul_of_disjoint_support
    (left right : Mode → Int)
    (hdisjoint : Disjoint (Function.support left)
      (Function.support right)) :
    (if left + right = 0 then (1 : Complex) else 0) =
      (if left = 0 then (1 : Complex) else 0) *
        (if right = 0 then (1 : Complex) else 0) := by
  by_cases hleft : left = 0
  · subst left
    simp
  by_cases hright : right = 0
  · subst right
    simp [hleft]
  have hadd : left + right ≠ 0 :=
    add_ne_zero_of_left_ne_zero_of_disjoint_support
      left right hleft hdisjoint
  simp [hleft, hright, hadd]

omit [Nonempty I] in
/-- Aggregate charges add over disjoint index blocks. -/
theorem indexedSignedTreeBlockCharge_union
    (entry : I → SignedInteractionTree Mode)
    {left right : Finset I} (hindex : Disjoint left right) :
    indexedSignedTreeBlockCharge entry (left ∪ right) =
      indexedSignedTreeBlockCharge entry left +
        indexedSignedTreeBlockCharge entry right := by
  unfold indexedSignedTreeBlockCharge
  rw [Finset.sum_union hindex]

omit [Nonempty I] in
/-- Exact arbitrary-order initial Haar factorization when the two aggregate
charge supports are disjoint. -/
theorem initialHaarSignedTreeBlockMoment_union_eq_mul_of_disjoint_chargeSupport
    (entry : I → SignedInteractionTree Mode)
    {left right : Finset I} (hindex : Disjoint left right)
    (hcharge : Disjoint
      (Function.support (indexedSignedTreeBlockCharge entry left))
      (Function.support (indexedSignedTreeBlockCharge entry right))) :
    initialHaarSignedTreeBlockMoment entry (left ∪ right) =
      initialHaarSignedTreeBlockMoment entry left *
        initialHaarSignedTreeBlockMoment entry right := by
  unfold initialHaarSignedTreeBlockMoment
  rw [indexedSignedTreeBlockCharge_union entry hindex]
  exact haarChargeSelector_add_eq_mul_of_disjoint_support
    _ _ hcharge

omit [Nonempty I] in
/-- Physical form of the factorization premise: no individual base mode is
used by both clusters. -/
theorem initialHaarSignedTreeBlockMoment_union_eq_mul_of_disjoint_clusters
    (entry : I → SignedInteractionTree Mode)
    {left right : Finset I} (hindex : Disjoint left right)
    (hcluster : Disjoint
      (indexedSignedTreeClusterModeSupport entry left)
      (indexedSignedTreeClusterModeSupport entry right)) :
    initialHaarSignedTreeBlockMoment entry (left ∪ right) =
      initialHaarSignedTreeBlockMoment entry left *
        initialHaarSignedTreeBlockMoment entry right := by
  apply initialHaarSignedTreeBlockMoment_union_eq_mul_of_disjoint_chargeSupport
    entry hindex
  exact hcluster.mono
    (support_indexedSignedTreeBlockCharge_subset_clusterModeSupport
      entry left)
    (support_indexedSignedTreeBlockCharge_subset_clusterModeSupport
      entry right)

omit [Nonempty I] in
/-- The same two-cluster factorization holds simultaneously for every pair
of subblocks.  This is the initial finite-moment formulation of independence
needed by a propagation-of-chaos argument. -/
theorem initialHaarSignedTreeSubblockMoment_factorizes_of_disjoint_clusters
    (entry : I → SignedInteractionTree Mode)
    {left right : Finset I} (hindex : Disjoint left right)
    (hcluster : Disjoint
      (indexedSignedTreeClusterModeSupport entry left)
      (indexedSignedTreeClusterModeSupport entry right))
    {leftSub rightSub : Finset I}
    (hleftSub : leftSub ⊆ left) (hrightSub : rightSub ⊆ right) :
    initialHaarSignedTreeBlockMoment entry (leftSub ∪ rightSub) =
      initialHaarSignedTreeBlockMoment entry leftSub *
        initialHaarSignedTreeBlockMoment entry rightSub := by
  apply initialHaarSignedTreeBlockMoment_union_eq_mul_of_disjoint_clusters
  · exact hindex.mono hleftSub hrightSub
  · exact hcluster.mono
      (indexedSignedTreeClusterModeSupport_mono entry hleftSub)
      (indexedSignedTreeClusterModeSupport_mono entry hrightSub)

omit [Nonempty I] in
/-- The actual iid mass/Haar-phase ensemble has the same arbitrary-order
subblock factorization.  Mass randomness is untouched; the assertion is the
exact product-Haar statement for the initial phase characters. -/
theorem actualIIDInitialSignedTreeSubblockMoment_factorizes_of_disjoint_clusters
    {Omega : Type*} [MeasurableSpace Omega]
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N]
    (entry : I → SignedInteractionTree (Lattice.Site N))
    {left right : Finset I} (hindex : Disjoint left right)
    (hcluster : Disjoint
      (indexedSignedTreeClusterModeSupport entry left)
      (indexedSignedTreeClusterModeSupport entry right))
    {leftSub rightSub : Finset I}
    (hleftSub : leftSub ⊆ left) (hrightSub : rightSub ⊆ right) :
    actualIIDInitialSignedTreeBlockMoment ensemble entry
        (leftSub ∪ rightSub) =
      actualIIDInitialSignedTreeBlockMoment ensemble entry leftSub *
        actualIIDInitialSignedTreeBlockMoment ensemble entry rightSub := by
  rw [actualIIDInitialSignedTreeBlockMoment_eq_selector,
    actualIIDInitialSignedTreeBlockMoment_eq_selector,
    actualIIDInitialSignedTreeBlockMoment_eq_selector]
  exact initialHaarSignedTreeSubblockMoment_factorizes_of_disjoint_clusters
    entry hindex hcluster hleftSub hrightSub

end

end ArchonPhysics.FreeFPUTInitialHaarDisjointClusterFactorization
