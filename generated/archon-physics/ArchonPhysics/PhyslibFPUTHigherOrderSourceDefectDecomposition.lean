import ArchonPhysics.PhyslibFPUTHigherOrderClusterFactorizationPropagation

/-!
# Decomposition of the higher-order FPUT factorization source defect

The derivative of a cluster-factorization defect contains a source defect.
Calling that source `small` is not yet an RPA proof.  This module resolves it
into two concrete mixed correlations: insert the nonlinear Hamiltonian source
in the left cluster and correlate it with the right cluster, or conversely.

The first theorem is the exact arbitrary-order Leibniz split on disjoint
blocks.  Finite ensemble averaging then shows that the full source defect is
the sum of the two source/moment factorization defects.  The last section
specializes the identity to the verified full coercive alpha-beta FPUT source.

Thus the positive-time high-order task is explicit: bound mixed correlations
containing one genuine nonlinear source insertion.  No re-Haarization,
Markov assumption, or pairwise-to-higher-order implication occurs here.
-/

namespace ArchonPhysics.PhyslibFPUTHigherOrderSourceDefectDecomposition

open ArchonPhysics
open ArchonPhysics.CoerciveHamiltonianPhyslib
open ArchonPhysics.FinitePhaseMonomials
open ArchonPhysics.MassWeightedHamiltonianDynamics
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.PhyslibFPUTCoercivePositiveTimeCumulantHierarchy
open ArchonPhysics.PhyslibFPUTHigherOrderClusterFactorizationPropagation
open ArchonPhysics.PhyslibFPUTPositiveTimeCumulantHierarchy

noncomputable section

variable {I Omega : Type*}
  [Fintype I] [DecidableEq I] [Nonempty I]
  [Fintype Omega] [DecidableEq Omega]

/-! ## Pointwise arbitrary-block source split -/

/-- The one-slot insertion on a disjoint union is exactly the product-rule
sum of the two block insertions. -/
theorem signedBlockSlotInsertion_union
    (path source : I → Real → Complex)
    {left right : Finset I} (hindex : Disjoint left right)
    (time : Real)
    (hpath : ∀ i ∈ left ∪ right,
      HasDerivAt (path i) (source i time) time) :
    signedBlockSlotInsertion path source (left ∪ right) time =
      signedBlockSlotInsertion path source left time *
          signedBlockMonomial path right time +
        signedBlockMonomial path left time *
          signedBlockSlotInsertion path source right time := by
  have hunion := hasDerivAt_signedBlockMonomial
    path source (left ∪ right) time hpath
  have hleft := hasDerivAt_signedBlockMonomial
    path source left time (fun i hi ↦ hpath i (Finset.mem_union_left right hi))
  have hright := hasDerivAt_signedBlockMonomial
    path source right time (fun i hi ↦ hpath i (Finset.mem_union_right left hi))
  have hproduct := hleft.mul hright
  have hunion' : HasDerivAt
      (fun s ↦ signedBlockMonomial path left s *
        signedBlockMonomial path right s)
      (signedBlockSlotInsertion path source (left ∪ right) time) time := by
    convert hunion using 1
    funext s
    simp only [signedBlockMonomial]
    rw [Finset.prod_union hindex]
  exact hunion'.unique hproduct

/-! ## Finite weighted mixed correlations -/

/-- Weighted mixed correlation with a source inserted in the left block and
an ordinary moment in the right block. -/
def finiteWeightedInsertionMoment
    (weight : Omega → Real)
    (path source : Omega → I → Real → Complex)
    (left right : Finset I) (time : Real) : Complex :=
  ∑ omega, (weight omega : Complex) *
    (signedBlockSlotInsertion (path omega) (source omega) left time *
      signedBlockMonomial (path omega) right time)

/-- Weighted mixed correlation with an ordinary left block and a source
inserted in the right block. -/
def finiteWeightedMomentInsertion
    (weight : Omega → Real)
    (path source : Omega → I → Real → Complex)
    (left right : Finset I) (time : Real) : Complex :=
  ∑ omega, (weight omega : Complex) *
    (signedBlockMonomial (path omega) left time *
      signedBlockSlotInsertion (path omega) (source omega) right time)

/-- Exact finite-ensemble source split across two disjoint blocks. -/
theorem finiteWeightedBlockInsertion_union
    (weight : Omega → Real)
    (path source : Omega → I → Real → Complex)
    {left right : Finset I} (hindex : Disjoint left right)
    (time : Real)
    (hpath : ∀ omega i, i ∈ left ∪ right →
      HasDerivAt (path omega i) (source omega i time) time) :
    finiteWeightedBlockInsertion weight path source
        (left ∪ right) time =
      finiteWeightedInsertionMoment weight path source left right time +
        finiteWeightedMomentInsertion weight path source left right time := by
  unfold finiteWeightedBlockInsertion finiteWeightedInsertionMoment
    finiteWeightedMomentInsertion
  simp_rw [signedBlockSlotInsertion_union
    (path := path _) (source := source _) hindex time (hpath _)]
  simp only [mul_add, Finset.sum_add_distrib]

/-- Failure of a left-source mixed correlation to factorize. -/
def leftSourceMomentFactorizationDefect
    (weight : Omega → Real)
    (path source : Omega → I → Real → Complex)
    (left right : Finset I) (time : Real) : Complex :=
  finiteWeightedInsertionMoment weight path source left right time -
    finiteWeightedBlockInsertion weight path source left time *
      finiteWeightedBlockMoment weight path right time

/-- Failure of a right-source mixed correlation to factorize. -/
def rightMomentSourceFactorizationDefect
    (weight : Omega → Real)
    (path source : Omega → I → Real → Complex)
    (left right : Finset I) (time : Real) : Complex :=
  finiteWeightedMomentInsertion weight path source left right time -
    finiteWeightedBlockMoment weight path left time *
      finiteWeightedBlockInsertion weight path source right time

/-- The full higher-order factorization source defect is exactly the sum of
the two mixed source/moment correlation defects. -/
theorem blockFactorizationDefectSource_finiteWeighted_eq_sum
    (weight : Omega → Real)
    (path source : Omega → I → Real → Complex)
    {left right : Finset I} (hindex : Disjoint left right)
    (time : Real)
    (hpath : ∀ omega i, i ∈ left ∪ right →
      HasDerivAt (path omega i) (source omega i time) time) :
    blockFactorizationDefectSource
        (finiteWeightedBlockMoment weight path)
        (finiteWeightedBlockInsertion weight path source)
        left right time =
      leftSourceMomentFactorizationDefect
          weight path source left right time +
        rightMomentSourceFactorizationDefect
          weight path source left right time := by
  unfold blockFactorizationDefectSource
    leftSourceMomentFactorizationDefect
    rightMomentSourceFactorizationDefect
  rw [finiteWeightedBlockInsertion_union
    weight path source hindex time hpath]
  ring

/-- Quantitative reduction of source-defect control to the two explicit
mixed source/moment correlations. -/
theorem norm_blockFactorizationDefectSource_finiteWeighted_le
    (weight : Omega → Real)
    (path source : Omega → I → Real → Complex)
    {left right : Finset I} (hindex : Disjoint left right)
    (time : Real)
    (hpath : ∀ omega i, i ∈ left ∪ right →
      HasDerivAt (path omega i) (source omega i time) time) :
    ‖blockFactorizationDefectSource
        (finiteWeightedBlockMoment weight path)
        (finiteWeightedBlockInsertion weight path source)
        left right time‖ ≤
      ‖leftSourceMomentFactorizationDefect
          weight path source left right time‖ +
        ‖rightMomentSourceFactorizationDefect
          weight path source left right time‖ := by
  rw [blockFactorizationDefectSource_finiteWeighted_eq_sum
    weight path source hindex time hpath]
  exact norm_add_le _ _

/-! ## Actual full coercive alpha-beta FPUT specialization -/

/-- Exact source-defect decomposition for actual full alpha-beta FPUT
Hamiltonian trajectories.  Both terms on the right are concrete finite
ensemble mixed correlations of the canonical modal path and verified
coercive source. -/
theorem actualFiniteCoerciveClusterFactorizationDefectSource_eq_sum
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
    {left right : Finset I} (hindex : Disjoint left right)
    (time : Real) :
    actualFiniteCoerciveClusterFactorizationDefectSource
        weight mass kappa beta g entry p q left right time =
      leftSourceMomentFactorizationDefect weight
          (actualFiniteCubicEnsemblePath mass entry p q)
          (actualFiniteCoerciveEnsembleSource
            mass kappa beta g entry q)
          left right time +
        rightMomentSourceFactorizationDefect weight
          (actualFiniteCubicEnsemblePath mass entry p q)
          (actualFiniteCoerciveEnsembleSource
            mass kappa beta g entry q)
          left right time := by
  unfold actualFiniteCoerciveClusterFactorizationDefectSource
    actualFiniteCubicEnsembleBlockMoment
    actualFiniteCoerciveEnsembleBlockInsertion
  apply blockFactorizationDefectSource_finiteWeighted_eq_sum
    weight
      (actualFiniteCubicEnsemblePath mass entry p q)
      (actualFiniteCoerciveEnsembleSource mass kappa beta g entry q)
      hindex time
  intro omega i _hi
  exact hasDerivAt_signedPhyslibInteractionModePath_coercive
    (mass omega) kappa beta g (entry i).1 (entry i).2
      (p omega) (q omega) (hp omega) (hq omega)
      (hHamilton omega) (homega omega i) time

/-- Actual full-potential source-defect bound by the two resolved mixed
correlation defects. -/
theorem norm_actualFiniteCoerciveClusterFactorizationDefectSource_le
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
    {left right : Finset I} (hindex : Disjoint left right)
    (time : Real) :
    ‖actualFiniteCoerciveClusterFactorizationDefectSource
        weight mass kappa beta g entry p q left right time‖ ≤
      ‖leftSourceMomentFactorizationDefect weight
          (actualFiniteCubicEnsemblePath mass entry p q)
          (actualFiniteCoerciveEnsembleSource
            mass kappa beta g entry q)
          left right time‖ +
        ‖rightMomentSourceFactorizationDefect weight
          (actualFiniteCubicEnsemblePath mass entry p q)
          (actualFiniteCoerciveEnsembleSource
            mass kappa beta g entry q)
          left right time‖ := by
  rw [actualFiniteCoerciveClusterFactorizationDefectSource_eq_sum
    weight mass kappa beta g entry p q hp hq hHamilton homega hindex time]
  exact norm_add_le _ _

end

end ArchonPhysics.PhyslibFPUTHigherOrderSourceDefectDecomposition
