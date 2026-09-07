import Submission.Kakeya.ConvexFactoring.JointTubeFactoring
import Family8Grounding.Family8Prop66AOuterInnerProductAlgebraV1
import Mathlib.Tactic

/-!
# Joint tube factoring supplies the exact Proposition 6.6(A) count product, V4

`JointTubeFactoring` selects an exact-cardinality parent bucket and builds a
literal coarse tube partition with branching loss one. Thus its active fine
count is exactly `active coarse count * branching`. The same actual branching
is used in Equation (46), so Equations (45) and (46) multiply by the existing
audited identity, without an independent inner-count hypothesis.

V1 is a failed namespace/unfolding draft, V2 a namespace-typo draft, and V3 a
linter-only draft. None of them is imported.
-/

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8JointTubeFactoringExactUniformProp66AProductV4

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.JointTubeFactoring
open Submission.Kakeya.Uniformity
open Family8Prop66AFrostmanAspectGainAlgebraV1
open Family8Prop66AOuterInnerProductAlgebraV1

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false

variable {delta rho : NNReal} {iota kappa : Type*}
  [Fintype iota] [Fintype kappa]
  [DecidableEq iota] [DecidableEq kappa]
  {fine : UniformTubeFamily delta iota}
  {coarse : UniformTubeFamily rho kappa}

/-- Branching loss one makes every active fibre have exactly the common
branching cardinality. -/
theorem fiber_card_eq_branching_of_branchingLoss_eq_one
    (P : CoarseTubePartition fine coarse)
    (hloss : P.branchingLoss = 1) {k : kappa}
    (hk : k ∈ P.coarseIndices) :
    (P.fiber k).card = P.branching := by
  change (P.index.fiber k).card = P.branching
  apply Nat.le_antisymm
  · simpa only [hloss, one_mul] using
      P.fiber_card_le_loss_mul_branching k hk
  · simpa only [hloss, one_mul] using
      P.branching_le_loss_mul_fiber k hk

/-- Exact fibre-cardinality uniformity converts the genuine fibre
decomposition into the literal product of active parents and branching. -/
theorem fineIndices_card_eq_coarseIndices_card_mul_branching_of_branchingLoss_eq_one
    (P : CoarseTubePartition fine coarse)
    (hloss : P.branchingLoss = 1) :
    P.fineIndices.card = P.coarseIndices.card * P.branching := by
  rw [P.card_fine_eq_sum_card_fiber]
  calc
    (∑ k ∈ P.coarseIndices, (P.fiber k).card) =
        ∑ _k ∈ P.coarseIndices, P.branching := by
      apply Finset.sum_congr rfl
      intro k hk
      exact fiber_card_eq_branching_of_branchingLoss_eq_one P hloss hk
    _ = P.coarseIndices.card * P.branching := by simp

/-- Eq.(45) and Eq.(46), on the same literal exact-uniform partition, multiply
to the Proposition 6.6(A) factor for its selected active fine family. -/
theorem outerFactor_mul_innerFactor_eq_fineIndices_frostmanFactor
    (P : CoarseTubePartition fine coarse)
    (hloss : P.branchingLoss = 1)
    {a b : NNReal} {CF : ENNReal} {epsilon beta : Real}
    (hdelta : 0 < delta) (ha : 0 < a) (hb : 0 < b)
    (hbeta : 0 ≤ beta) (hbetaOne : beta ≤ 1) :
    proposition66AOuterFactor delta a b P.coarseIndices.card
          CF epsilon beta *
        proposition66AInnerFactor delta a b P.branching epsilon beta =
      proposition66AFrostmanFactor delta a b P.fineIndices.card
        CF epsilon beta := by
  exact proposition66AOuterFactor_mul_innerFactor_eq_frostmanFactor
    hdelta ha hb hbeta hbetaOne
      (fineIndices_card_eq_coarseIndices_card_mul_branching_of_branchingLoss_eq_one
        P hloss)

/-- The real efficient-cover producer returns a same-data exact-uniform
partition and the exact outer-times-inner scalar identity simultaneously.
The selected uniform families use the original tube maps definitionally. -/
theorem exists_jointTubeFactoring_with_exactUniform_prop66A_product
    (fine : UniformTubeFamily delta iota)
    (coarse : UniformTubeFamily rho kappa)
    (active : Finset iota) (candidates : Finset kappa)
    (parent : iota → kappa) (A L : ENNReal)
    (hdelta : 0 < delta) (hscale : delta ≤ rho)
    (hactive : active.Nonempty)
    (hactiveRefined : active ⊆ fine.refinement.refined)
    (hcandidatesRefined : candidates ⊆ coarse.refinement.refined)
    (hparentCandidate : ∀ i ∈ active, parent i ∈ candidates)
    (hcontained : ∀ i ∈ active,
      (fine.tubes i).carrier ⊆ (coarse.tubes (parent i)).carrier)
    (hA0 : A ≠ 0) (hAtop : A ≠ ∞)
    (hL0 : L ≠ 0) (hLtop : L ≠ ∞)
    (hfineKT : IsKatzTaoOn A fine.bodyFamily active)
    (hcoverCost :
      A * (∑ k ∈ occupiedParents active parent,
        volume (coarse.tubes k).carrier) ≤
      L * bodyMassOn fine.bodyFamily active)
    {a b : NNReal} {CF : ENNReal} {epsilon beta : Real}
    (ha : 0 < a) (hb : 0 < b)
    (hbeta : 0 ≤ beta) (hbetaOne : beta ≤ 1) :
    ∃ (level : Fin (Fintype.card iota + 1))
        (selected : Finset kappa) (selectedFine : Finset iota)
        (fine' : UniformTubeFamily delta iota)
        (coarse' : UniformTubeFamily rho kappa)
        (P : CoarseTubePartition fine' coarse'),
      (∀ i, fine'.tubes i = fine.tubes i) ∧
      (∀ k, coarse'.tubes k = coarse.tubes k) ∧
      P.index = selectedIndexFactorization active parent selected ∧
      P.branching = level.1 ∧ P.branchingLoss = 1 ∧
      WithinFactor (2 * (Fintype.card iota + 1))
        (bodyMassOn fine.bodyFamily active)
        (bodyMassOn fine'.bodyFamily P.fineIndices) ∧
      selectedFine.Nonempty ∧ selected.Nonempty ∧
      selectedFine ⊆ active ∧ selected ⊆ candidates ∧
      (∀ k ∈ P.coarseIndices, (P.fiber k).card = level.1) ∧
      IsKatzTaoOn (2 * L) coarse'.bodyFamily P.coarseIndices ∧
      (∀ k ∈ P.coarseIndices,
        IsFrostmanOn (2 * L) fine'.bodyFamily (P.fiber k)
          (coarse'.bodyFamily k)) ∧
      proposition66AOuterFactor delta a b P.coarseIndices.card
            CF epsilon beta *
          proposition66AInnerFactor delta a b P.branching epsilon beta =
        proposition66AFrostmanFactor delta a b P.fineIndices.card
          CF epsilon beta := by
  obtain ⟨level, selected, selectedFine, fine', coarse', P,
      _hselected, _hselectedFine, hfineTubes, hcoarseTubes,
      _hfineProfile, _hcoarseProfile, hindex, hbranching, hloss,
      hretain, hselectedFineNonempty, hselectedNonempty,
      hselectedFineSub, hselectedSub, hfiber, hcoarseKT,
      hfiberFrostman⟩ :=
    exists_jointTubeFactoring fine coarse active candidates parent A L
      hdelta hscale hactive hactiveRefined hcandidatesRefined
      hparentCandidate hcontained hA0 hAtop hL0 hLtop hfineKT hcoverCost
  refine ⟨level, selected, selectedFine, fine', coarse', P,
    hfineTubes, hcoarseTubes, hindex, hbranching, hloss, hretain,
    hselectedFineNonempty, hselectedNonempty, hselectedFineSub,
    hselectedSub, hfiber, hcoarseKT, hfiberFrostman, ?_⟩
  exact outerFactor_mul_innerFactor_eq_fineIndices_frostmanFactor
    P hloss hdelta ha hb hbeta hbetaOne

#print axioms fiber_card_eq_branching_of_branchingLoss_eq_one
#print axioms
  fineIndices_card_eq_coarseIndices_card_mul_branching_of_branchingLoss_eq_one
#print axioms outerFactor_mul_innerFactor_eq_fineIndices_frostmanFactor
#print axioms exists_jointTubeFactoring_with_exactUniform_prop66A_product

end
end Family8JointTubeFactoringExactUniformProp66AProductV4
