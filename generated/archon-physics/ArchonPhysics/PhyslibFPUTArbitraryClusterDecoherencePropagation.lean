import ArchonPhysics.PhyslibFPUTHigherOrderClusterFactorizationPropagation

/-!
# Arbitrary many-cluster propagation of FPUT decoherence

Pairwise phase decorrelation is not a propagation-of-chaos statement.  At
fixed arbitrary order one must compare a joint moment of several disjoint
clusters with the product of all cluster moments.  This module performs that
upgrade without replacing the Hamiltonian law at an intermediate time.

The clusters are ordered only to write an exact telescoping identity.  At
step `n`, the already accumulated cluster union is compared with cluster
`n`.  Consequently every error on the right is an actual two-cluster
factorization defect on the same coherent trajectory.  The final theorem
specializes the construction to the full coercive alpha-beta FPUT source.

The remaining scientific input is displayed honestly: every prefix source
defect must be small on the kinetic interval.  No pairwise-RPA premise is
promoted to a higher-order conclusion, and no resonant balanced moment is
discarded.
-/

namespace ArchonPhysics.PhyslibFPUTArbitraryClusterDecoherencePropagation

open ArchonPhysics
open ArchonPhysics.CoerciveHamiltonianPhyslib
open ArchonPhysics.FinitePhaseMonomials
open ArchonPhysics.FreeFPUTArbitraryOrderInitialHaarSelection
open ArchonPhysics.FreeFPUTInitialHaarConnectedCumulant
open ArchonPhysics.FreeFPUTInitialHaarDisjointClusterFactorization
open ArchonPhysics.MassWeightedHamiltonianDynamics
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.PhyslibFPUTBinaryInteractionTreeCouples
open ArchonPhysics.PhyslibFPUTCoercivePositiveTimeCumulantHierarchy
open ArchonPhysics.PhyslibFPUTHigherOrderClusterFactorizationPropagation
open ArchonPhysics.PhyslibFPUTPositiveTimeCumulantHierarchy

noncomputable section

variable {I : Type*} [Fintype I] [DecidableEq I]

/-! ## Ordered algebraic telescope -/

/-- Union of the first `count` clusters.  The recursive presentation keeps
the later factorization proof independent of a choice of enumeration lemma
for `Finset.range`. -/
def orderedClusterUnion (cluster : Nat → Finset I) : Nat → Finset I
  | 0 => ∅
  | n + 1 => orderedClusterUnion cluster n ∪ cluster n

/-- Product of the first `count` cluster moments. -/
def orderedClusterMomentProduct
    (blockMoment : Finset I → Real → Complex)
    (cluster : Nat → Finset I) (time : Real) : Nat → Complex
  | 0 => 1
  | n + 1 =>
      orderedClusterMomentProduct blockMoment cluster time n *
        blockMoment (cluster n) time

/-- Failure of factorization for an arbitrary finite ordered family of
clusters. -/
def orderedClusterFactorizationDefect
    (blockMoment : Finset I → Real → Complex)
    (cluster : Nat → Finset I) (count : Nat) (time : Real) : Complex :=
  blockMoment (orderedClusterUnion cluster count) time -
    orderedClusterMomentProduct blockMoment cluster time count

/-- Exact recursion: a many-cluster defect is one genuine prefix-versus-next
binary defect plus the earlier many-cluster defect times the next moment. -/
theorem orderedClusterFactorizationDefect_succ
    (blockMoment : Finset I → Real → Complex)
    (cluster : Nat → Finset I) (count : Nat) (time : Real) :
    orderedClusterFactorizationDefect blockMoment cluster (count + 1) time =
      blockFactorizationDefect blockMoment
          (orderedClusterUnion cluster count) (cluster count) time +
        orderedClusterFactorizationDefect blockMoment cluster count time *
          blockMoment (cluster count) time := by
  simp only [orderedClusterFactorizationDefect, orderedClusterUnion,
    orderedClusterMomentProduct, blockFactorizationDefect]
  ring

/-- Recursive sharp error budget.  It records the later cluster moments
explicitly instead of silently imposing a unit bound on them. -/
def orderedClusterFactorizationErrorBound
    (blockMoment : Finset I → Real → Complex)
    (cluster : Nat → Finset I) (epsilon : Nat → Real)
    (time : Real) : Nat → Real
  | 0 => ‖blockMoment ∅ time - 1‖
  | n + 1 =>
      epsilon n * |time| +
        orderedClusterFactorizationErrorBound
            blockMoment cluster epsilon time n *
          ‖blockMoment (cluster n) time‖

/-- Arbitrary finite-order factorization follows from the corresponding
prefix source-defect estimates.  This statement is purely algebraic and
does not assume that pairwise decorrelation implies the hypotheses. -/
theorem norm_orderedClusterFactorizationDefect_le
    (blockMoment : Finset I → Real → Complex)
    (cluster : Nat → Finset I) (epsilon : Nat → Real)
    (time : Real)
    (hbinary : ∀ n,
      ‖blockFactorizationDefect blockMoment
          (orderedClusterUnion cluster n) (cluster n) time‖ ≤
        epsilon n * |time|)
    (count : Nat) :
    ‖orderedClusterFactorizationDefect
        blockMoment cluster count time‖ ≤
      orderedClusterFactorizationErrorBound
        blockMoment cluster epsilon time count := by
  induction count with
  | zero =>
      change ‖blockMoment ∅ time - 1‖ ≤
        ‖blockMoment ∅ time - 1‖
      exact le_rfl
  | succ n ih =>
      rw [orderedClusterFactorizationDefect_succ]
      calc
        ‖blockFactorizationDefect blockMoment
              (orderedClusterUnion cluster n) (cluster n) time +
            orderedClusterFactorizationDefect
                blockMoment cluster n time *
              blockMoment (cluster n) time‖
            ≤ ‖blockFactorizationDefect blockMoment
                  (orderedClusterUnion cluster n) (cluster n) time‖ +
                ‖orderedClusterFactorizationDefect
                    blockMoment cluster n time *
                  blockMoment (cluster n) time‖ := norm_add_le _ _
        _ = ‖blockFactorizationDefect blockMoment
                  (orderedClusterUnion cluster n) (cluster n) time‖ +
              ‖orderedClusterFactorizationDefect
                  blockMoment cluster n time‖ *
                ‖blockMoment (cluster n) time‖ := by rw [norm_mul]
        _ ≤ epsilon n * |time| +
              orderedClusterFactorizationErrorBound
                  blockMoment cluster epsilon time n *
                ‖blockMoment (cluster n) time‖ :=
          add_le_add (hbinary n)
            (mul_le_mul_of_nonneg_right ih (norm_nonneg _))
        _ = orderedClusterFactorizationErrorBound
              blockMoment cluster epsilon time (n + 1) := rfl

/-- For normalized cluster observables, the recursive arbitrary-order error
budget is bounded by the sum of all prefix source errors.  Nonnegativity is
kept explicit; it is not inferred from a signed asymptotic expansion. -/
theorem orderedClusterFactorizationErrorBound_le_sum
    (blockMoment : Finset I → Real → Complex)
    (cluster : Nat → Finset I) (epsilon : Nat → Real)
    (time : Real)
    (hempty : blockMoment ∅ time = 1)
    (hmoment : ∀ n, ‖blockMoment (cluster n) time‖ ≤ 1)
    (hepsilon : ∀ n, 0 ≤ epsilon n)
    (count : Nat) :
    orderedClusterFactorizationErrorBound
        blockMoment cluster epsilon time count ≤
      (∑ n ∈ Finset.range count, epsilon n) * |time| := by
  induction count with
  | zero =>
      simp [orderedClusterFactorizationErrorBound, hempty]
  | succ n ih =>
      rw [Finset.sum_range_succ]
      change epsilon n * |time| +
          orderedClusterFactorizationErrorBound
              blockMoment cluster epsilon time n *
            ‖blockMoment (cluster n) time‖ ≤
        ((∑ i ∈ Finset.range n, epsilon i) + epsilon n) * |time|
      have hsum : 0 ≤ ∑ i ∈ Finset.range n, epsilon i :=
        Finset.sum_nonneg fun i _hi ↦ hepsilon i
      have hprevious :
          0 ≤ (∑ i ∈ Finset.range n, epsilon i) * |time| :=
        mul_nonneg hsum (abs_nonneg time)
      calc
        epsilon n * |time| +
              orderedClusterFactorizationErrorBound
                  blockMoment cluster epsilon time n *
                ‖blockMoment (cluster n) time‖
            ≤ epsilon n * |time| +
                ((∑ i ∈ Finset.range n, epsilon i) * |time|) *
                  ‖blockMoment (cluster n) time‖ :=
          add_le_add le_rfl
            (mul_le_mul_of_nonneg_right
              ih (norm_nonneg _))
        _ ≤ epsilon n * |time| +
              ((∑ i ∈ Finset.range n, epsilon i) * |time|) * 1 :=
          add_le_add le_rfl
            (mul_le_mul_of_nonneg_left
              (hmoment n) hprevious)
        _ = ((∑ i ∈ Finset.range n, epsilon i) + epsilon n) *
              |time| := by ring

/-- Clean arbitrary fixed-order bound for normalized cluster moments. -/
theorem norm_orderedClusterFactorizationDefect_le_sum
    (blockMoment : Finset I → Real → Complex)
    (cluster : Nat → Finset I) (epsilon : Nat → Real)
    (time : Real)
    (hbinary : ∀ n,
      ‖blockFactorizationDefect blockMoment
          (orderedClusterUnion cluster n) (cluster n) time‖ ≤
        epsilon n * |time|)
    (hempty : blockMoment ∅ time = 1)
    (hmoment : ∀ n, ‖blockMoment (cluster n) time‖ ≤ 1)
    (hepsilon : ∀ n, 0 ≤ epsilon n)
    (count : Nat) :
    ‖orderedClusterFactorizationDefect
        blockMoment cluster count time‖ ≤
      (∑ n ∈ Finset.range count, epsilon n) * |time| :=
  (norm_orderedClusterFactorizationDefect_le
      blockMoment cluster epsilon time hbinary count).trans
    (orderedClusterFactorizationErrorBound_le_sum
      blockMoment cluster epsilon time hempty hmoment hepsilon count)

/-- Fixed arbitrary-order propagation of chaos in a joint scaling limit.
The binary premises are *prefix-versus-next-cluster* limits, so for large
`n` they are genuinely high-order decoherence statements rather than merely
two-mode phase cancellation.  Convergence of the individual cluster moments
keeps all balanced/resonant limiting moments visible. -/
theorem tendsto_orderedClusterFactorizationDefect_zero
    (blockMoment : Nat → Finset I → Real → Complex)
    (cluster : Nat → Finset I) (time : Nat → Real)
    (limitMoment : Nat → Complex)
    (hempty : Filter.Tendsto
      (fun scale ↦ blockMoment scale ∅ (time scale))
      Filter.atTop (nhds 1))
    (hbinary : ∀ n, Filter.Tendsto
      (fun scale ↦ blockFactorizationDefect (blockMoment scale)
        (orderedClusterUnion cluster n) (cluster n) (time scale))
      Filter.atTop (nhds 0))
    (hmoment : ∀ n, Filter.Tendsto
      (fun scale ↦ blockMoment scale (cluster n) (time scale))
      Filter.atTop (nhds (limitMoment n)))
    (count : Nat) :
    Filter.Tendsto
      (fun scale ↦ orderedClusterFactorizationDefect
        (blockMoment scale) cluster count (time scale))
      Filter.atTop (nhds 0) := by
  induction count with
  | zero =>
      have hone : Filter.Tendsto
          (fun _ : Nat ↦ (1 : Complex)) Filter.atTop (nhds 1) :=
        tendsto_const_nhds
      have hbase := hempty.sub hone
      simpa [orderedClusterFactorizationDefect,
        orderedClusterUnion, orderedClusterMomentProduct] using hbase
  | succ n ih =>
      have hstep := (hbinary n).add (ih.mul (hmoment n))
      simpa only [orderedClusterFactorizationDefect_succ,
        zero_mul, add_zero] using hstep

/-! ## Exact arbitrary-order initial Haar factorization -/

variable {Mode : Type*} [Fintype Mode] [DecidableEq Mode] [Nonempty I]

/-- Sequential disjointness of index clusters and their base-mode supports
gives exact factorization of every finite initial Haar cluster family. -/
theorem orderedClusterFactorizationDefect_zero_of_initialHaar
    (entry : I → SignedInteractionTree Mode)
    (blockMoment : Finset I → Real → Complex)
    (hinitial : ∀ block,
      blockMoment block 0 = initialHaarSignedTreeBlockMoment entry block)
    (cluster : Nat → Finset I)
    (hindex : ∀ n,
      Disjoint (orderedClusterUnion cluster n) (cluster n))
    (hcluster : ∀ n, Disjoint
      (indexedSignedTreeClusterModeSupport entry
        (orderedClusterUnion cluster n))
      (indexedSignedTreeClusterModeSupport entry (cluster n)))
    (count : Nat) :
    orderedClusterFactorizationDefect
      blockMoment cluster count 0 = 0 := by
  induction count with
  | zero =>
      unfold orderedClusterFactorizationDefect
      rw [hinitial]
      simp [orderedClusterUnion, orderedClusterMomentProduct,
        initialHaarSignedTreeBlockMoment, indexedSignedTreeBlockCharge]
  | succ n ih =>
      rw [orderedClusterFactorizationDefect_succ]
      rw [blockFactorizationDefect_zero_of_initialHaar_disjointClusters
        entry blockMoment hinitial (hindex n) (hcluster n)]
      simp [ih]

/-! ## Actual full coercive alpha-beta hierarchy -/

variable {Omega : Type*} [Fintype Omega]

/-- Actual full-potential many-cluster factorization defect on one coherent
finite ensemble of Hamiltonian trajectories. -/
def actualFiniteCoerciveOrderedClusterFactorizationDefect
    {N : Nat} [NeZero N]
    (weight : Omega → Real)
    (mass : Omega → Lattice.PositiveMassConfig N)
    (entry : I → PhaseSign × Lattice.Site N)
    (p q : Omega → Time → HilbertConfiguration N)
    (cluster : Nat → Finset I) (count : Nat) (time : Real) : Complex :=
  orderedClusterFactorizationDefect
    (actualFiniteCubicEnsembleBlockMoment weight mass entry p q)
    cluster count time

/-- The actual full alpha-beta hierarchy propagates arbitrary finite-order
decoherence from exact initial prefix factorization and quantitative bounds
on every prefix source defect.  These are precisely the high-order RPA /
recollision estimates that remain to be obtained from the microscopic
Hamiltonian; they are not replaced by a pairwise random-phase assumption. -/
theorem norm_actualFiniteCoerciveOrderedClusterFactorizationDefect_le
    {N : Nat} [NeZero N]
    (weight : Omega → Real)
    (mass : Omega → Lattice.PositiveMassConfig N)
    (kappa beta g : Real)
    (entry : I → PhaseSign × Lattice.Site N)
    (p q : Omega → Time → HilbertConfiguration N)
    (hp : ∀ omega, Differentiable Real (p omega))
    (hq : ∀ omega, Differentiable Real (q omega))
    (hHamilton : ∀ omega,
      SatisfiesHamiltonEquations (mass omega) kappa beta g
        (p omega) (q omega))
    (homega : ∀ omega i,
      0 < modeFrequency (mass omega) (entry i).2)
    (cluster : Nat → Finset I)
    (hzero : ∀ n,
      actualFiniteCoerciveClusterFactorizationDefect
        weight mass entry p q
          (orderedClusterUnion cluster n) (cluster n) 0 = 0)
    (time : Real) (epsilon : Nat → Real)
    (hsource : ∀ n, ∀ s ∈ Set.uIcc 0 time,
      ‖actualFiniteCoerciveClusterFactorizationDefectSource
          weight mass kappa beta g entry p q
            (orderedClusterUnion cluster n) (cluster n) s‖ ≤ epsilon n)
    (count : Nat) :
    ‖actualFiniteCoerciveOrderedClusterFactorizationDefect
        weight mass entry p q cluster count time‖ ≤
      orderedClusterFactorizationErrorBound
        (actualFiniteCubicEnsembleBlockMoment weight mass entry p q)
        cluster epsilon time count := by
  apply norm_orderedClusterFactorizationDefect_le
  intro n
  exact norm_actualFiniteCoerciveClusterFactorizationDefect_le
    weight mass kappa beta g entry p q hp hq hHamilton homega
      (orderedClusterUnion cluster n) (cluster n) (hzero n)
      time (epsilon n) (hsource n)

end

end ArchonPhysics.PhyslibFPUTArbitraryClusterDecoherencePropagation
