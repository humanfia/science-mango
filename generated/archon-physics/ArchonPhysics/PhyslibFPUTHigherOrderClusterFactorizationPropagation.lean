import ArchonPhysics.FreeFPUTInitialHaarDisjointClusterFactorization
import ArchonPhysics.PhyslibFPUTHigherOrderDecoherencePropagation

/-!
# Positive-time propagation criterion for higher-order cluster factorization

For two finite clusters of signed modal observables, define the exact
factorization defect

`D(t) = M_(left ∪ right)(t) - M_left(t) * M_right(t)`.

This file proves its exact derivative from the unclosed block-moment
hierarchy and the quantitative estimate `‖D(t)‖ ≤ epsilon * |t|` when the
source defect is bounded by `epsilon`.  It also connects the new disjoint
mode-cluster Haar theorem to the initial condition `D(0)=0`.

The final section instantiates the derivative by the actual full coercive
alpha-beta FPUT Hamiltonian source.  The smallness of the source defect on a
kinetic interval remains the high-order garden/recollision problem; it is not
assumed to follow from pairwise decorrelation.
-/

namespace ArchonPhysics.PhyslibFPUTHigherOrderClusterFactorizationPropagation

open ArchonPhysics
open ArchonPhysics.CoerciveHamiltonianPhyslib
open ArchonPhysics.FinitePhaseMonomials
open ArchonPhysics.FreeFPUTArbitraryOrderInitialHaarSelection
open ArchonPhysics.FreeFPUTInitialHaarConnectedCumulant
open ArchonPhysics.FreeFPUTInitialHaarDisjointClusterFactorization
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.PhyslibFPUTBinaryInteractionTreeCouples
open ArchonPhysics.PhyslibFPUTCoercivePositiveTimeCumulantHierarchy
open ArchonPhysics.PhyslibFPUTHigherOrderDecoherencePropagation
open ArchonPhysics.PhyslibFPUTPositiveTimeCumulantHierarchy

noncomputable section

variable {I : Type*} [Fintype I] [DecidableEq I]

/-! ## Abstract block hierarchy -/

/-- Difference between a mixed block moment and the product of the two
cluster moments. -/
def blockFactorizationDefect
    (blockMoment : Finset I → Real → Complex)
    (left right : Finset I) (time : Real) : Complex :=
  blockMoment (left ∪ right) time -
    blockMoment left time * blockMoment right time

/-- Exact source of the factorization defect: the full source insertion in
the mixed block minus the two product-rule insertions. -/
def blockFactorizationDefectSource
    (blockMoment blockSource : Finset I → Real → Complex)
    (left right : Finset I) (time : Real) : Complex :=
  blockSource (left ∪ right) time -
    (blockSource left time * blockMoment right time +
      blockMoment left time * blockSource right time)

/-- Exact arbitrary-order factorization-defect hierarchy. -/
theorem hasDerivAt_blockFactorizationDefect
    (blockMoment blockSource : Finset I → Real → Complex)
    (left right : Finset I) (time : Real)
    (hblock : ∀ block, HasDerivAt (blockMoment block)
      (blockSource block time) time) :
    HasDerivAt
      (fun s ↦ blockFactorizationDefect blockMoment left right s)
      (blockFactorizationDefectSource
        blockMoment blockSource left right time) time := by
  unfold blockFactorizationDefect blockFactorizationDefectSource
  change HasDerivAt
    (blockMoment (left ∪ right) -
      blockMoment left * blockMoment right) _ time
  exact (hblock (left ∪ right)).sub
    ((hblock left).mul (hblock right))

variable {Mode : Type*} [Fintype Mode] [DecidableEq Mode] [Nonempty I]

/-- The disjoint-cluster Haar theorem supplies exact zero initial
factorization defect, including total-charge-balanced collections. -/
theorem blockFactorizationDefect_zero_of_initialHaar_disjointClusters
    (entry : I → SignedInteractionTree Mode)
    (blockMoment : Finset I → Real → Complex)
    (hinitial : ∀ block,
      blockMoment block 0 = initialHaarSignedTreeBlockMoment entry block)
    {left right : Finset I} (hindex : Disjoint left right)
    (hcluster : Disjoint
      (indexedSignedTreeClusterModeSupport entry left)
      (indexedSignedTreeClusterModeSupport entry right)) :
    blockFactorizationDefect blockMoment left right 0 = 0 := by
  unfold blockFactorizationDefect
  rw [hinitial (left ∪ right), hinitial left, hinitial right,
    initialHaarSignedTreeBlockMoment_union_eq_mul_of_disjoint_clusters
      entry hindex hcluster]
  simp

/-- Quantitative fixed-order propagation of initial Haar factorization. -/
theorem norm_blockFactorizationDefect_le_of_initialHaar_disjointClusters
    (entry : I → SignedInteractionTree Mode)
    (blockMoment blockSource : Finset I → Real → Complex)
    (hinitial : ∀ block,
      blockMoment block 0 = initialHaarSignedTreeBlockMoment entry block)
    {left right : Finset I} (hindex : Disjoint left right)
    (hcluster : Disjoint
      (indexedSignedTreeClusterModeSupport entry left)
      (indexedSignedTreeClusterModeSupport entry right))
    (time epsilon : Real)
    (hblock : ∀ s ∈ Set.uIcc 0 time, ∀ block,
      HasDerivAt (blockMoment block) (blockSource block s) s)
    (hsource : ∀ s ∈ Set.uIcc 0 time,
      ‖blockFactorizationDefectSource
        blockMoment blockSource left right s‖ ≤ epsilon) :
    ‖blockFactorizationDefect blockMoment left right time‖ ≤
      epsilon * |time| := by
  apply norm_connectedCumulant_le_of_initial_eq_zero
  · exact blockFactorizationDefect_zero_of_initialHaar_disjointClusters
      entry blockMoment hinitial hindex hcluster
  · intro s hs
    exact hasDerivAt_blockFactorizationDefect
      blockMoment blockSource left right s (hblock s hs)
  · exact hsource

/-! ## Actual full coercive alpha-beta FPUT block hierarchy -/

variable {Omega : Type*} [Fintype Omega]

/-- Each actual finite-ensemble block moment differentiates by inserting the
full alpha-beta source in one signed modal slot. -/
theorem hasDerivAt_actualFiniteCoerciveEnsembleBlockMoment
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
    (block : Finset I) (time : Real) :
    HasDerivAt
      (fun s ↦ actualFiniteCubicEnsembleBlockMoment
        weight mass entry p q block s)
      (actualFiniteCoerciveEnsembleBlockInsertion
        weight mass kappa beta g entry p q block time) time := by
  apply hasDerivAt_finiteWeightedBlockMoment
  intro omega i _hi
  exact hasDerivAt_signedPhyslibInteractionModePath_coercive
    (mass omega) kappa beta g (entry i).1 (entry i).2
    (p omega) (q omega) (hp omega) (hq omega)
    (hHamilton omega) (homega omega i) time

/-- Actual full alpha-beta finite-ensemble cluster factorization defect. -/
def actualFiniteCoerciveClusterFactorizationDefect
    {N : Nat} [NeZero N]
    (weight : Omega → Real)
    (mass : Omega → Lattice.PositiveMassConfig N)
    (entry : I → PhaseSign × Lattice.Site N)
    (p q : Omega → Time → HilbertConfiguration N)
    (left right : Finset I) (time : Real) : Complex :=
  blockFactorizationDefect
    (actualFiniteCubicEnsembleBlockMoment weight mass entry p q)
    left right time

/-- Exact full alpha-beta source defect for the same two clusters. -/
def actualFiniteCoerciveClusterFactorizationDefectSource
    {N : Nat} [NeZero N]
    (weight : Omega → Real)
    (mass : Omega → Lattice.PositiveMassConfig N)
    (kappa beta g : Real)
    (entry : I → PhaseSign × Lattice.Site N)
    (p q : Omega → Time → HilbertConfiguration N)
    (left right : Finset I) (time : Real) : Complex :=
  blockFactorizationDefectSource
    (actualFiniteCubicEnsembleBlockMoment weight mass entry p q)
    (actualFiniteCoerciveEnsembleBlockInsertion
      weight mass kappa beta g entry p q)
    left right time

/-- Actual Hamiltonian derivative of the arbitrary-order cluster defect. -/
theorem hasDerivAt_actualFiniteCoerciveClusterFactorizationDefect
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
    (left right : Finset I) (time : Real) :
    HasDerivAt
      (fun s ↦ actualFiniteCoerciveClusterFactorizationDefect
        weight mass entry p q left right s)
      (actualFiniteCoerciveClusterFactorizationDefectSource
        weight mass kappa beta g entry p q left right time) time := by
  apply hasDerivAt_blockFactorizationDefect
  intro block
  exact hasDerivAt_actualFiniteCoerciveEnsembleBlockMoment
    weight mass kappa beta g entry p q hp hq hHamilton homega block time

/-- Honest positive-time approximate propagation-of-chaos endpoint for the
actual full alpha-beta finite ensemble.  Both initial factorization and the
source-defect bound remain explicit. -/
theorem norm_actualFiniteCoerciveClusterFactorizationDefect_le
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
    (left right : Finset I)
    (hzero : actualFiniteCoerciveClusterFactorizationDefect
      weight mass entry p q left right 0 = 0)
    (time epsilon : Real)
    (hsource : ∀ s ∈ Set.uIcc 0 time,
      ‖actualFiniteCoerciveClusterFactorizationDefectSource
        weight mass kappa beta g entry p q left right s‖ ≤ epsilon) :
    ‖actualFiniteCoerciveClusterFactorizationDefect
      weight mass entry p q left right time‖ ≤ epsilon * |time| := by
  apply norm_connectedCumulant_le_of_initial_eq_zero
  · exact hzero
  · intro s _hs
    exact hasDerivAt_actualFiniteCoerciveClusterFactorizationDefect
      weight mass kappa beta g entry p q hp hq hHamilton homega
      left right s
  · exact hsource

end

end ArchonPhysics.PhyslibFPUTHigherOrderClusterFactorizationPropagation
