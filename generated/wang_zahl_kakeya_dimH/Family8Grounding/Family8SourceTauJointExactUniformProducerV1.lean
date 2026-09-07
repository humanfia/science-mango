import Family8Grounding.Family8StickyJointExactUniformCoverCostV4
import Family8Grounding.Family8NormalizedCrossingSourceTauShadingV2
import Submission.Kakeya.ConvexFactoring.FactoringMultiplicityAssembly
import Mathlib.Tactic

/-!
# The canonical source-to-tau cover produces an exact-card joint partition

The source-to-`tau` cover is a literal `StickyScaleCover`.  Its source
Katz--Tao condition is inherited from the original actual datum, while its
global cover cost is automatic from tube-volume comparability.  Thus the
repository's real `JointTubeFactoring` producer applies without either a
cover-cost callback or a source-fine Katz--Tao callback.

The resulting exact-card partition also admits an actual
`FactoringMultiplicityAssembly.ExactAssembly` at its exact branching bound.
-/

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8SourceTauJointExactUniformProducerV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FactoringMultiplicityAssembly
open Submission.Kakeya.ConvexFactoring.JointTubeFactoring
open Submission.Kakeya.Uniformity
open Family8KatzTaoFrostmanPropertiesV1
open Family8NormalizedCrossingSourceTauShadingV2
open Family8Prop66AFrostmanAspectGainAlgebraV1
open Family8Prop66AOuterInnerProductAlgebraV1
open Family8JointTubeFactoringExactUniformProp66AProductV4
open Family8StickyJointExactUniformCoverCostV4
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCoherentIntervalProducerV1

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false

variable {delta rho : NNReal} {iota kappa : Type*}
  [Fintype iota] [Fintype kappa]
  [DecidableEq iota] [DecidableEq kappa]
  {fine : UniformTubeFamily delta iota}
  {coarse : UniformTubeFamily rho kappa}

/-- Exact-uniformity supplies the sharp fibre bound needed by the actual
multiplicity assembly.  This is a producer for every literal shading on the
selected fine family, not a stored conclusion. -/
theorem exists_exactAssembly_of_branchingLoss_eq_one
    (P : CoarseTubePartition fine coarse)
    (Y : Shading fine.bodyFamily)
    (hloss : P.branchingLoss = 1) :
    ∃ A : ExactAssembly P.asConvexFactorization Y
        (((P.branching + 1) * (P.branching + 1)) *
          (Fintype.card kappa + 1)),
      A.fineLevel ≤ P.branching ∧
      A.outerLevel ≤ Fintype.card kappa := by
  apply exists_exactAssembly_of_fiber_card_le
    P.asConvexFactorization Y P.branching
  intro k hk
  change k ∈ P.coarseIndices at hk
  change (P.fiber k).card ≤ P.branching
  exact (fiber_card_eq_branching_of_branchingLoss_eq_one P hloss hk).le

variable {sourceDelta : NNReal} {sourceIndex : Type}
  [Fintype sourceIndex] [DecidableEq sourceIndex]
  {depth : Nat}

/-- Nonzero mass on the canonical source restriction forces a literal active
source tube. -/
theorem sourceTauCover_activeFine_nonempty_of_restrictedMass_ne_zero
    (D : ActualTubeDatum sourceDelta sourceIndex)
    (C : CoherentStickyMultiscaleCover D.family)
    (S : FiniteScaleSequence sourceDelta depth) (m : Fin depth)
    (hsource :
      (IndexedShadingRefinement.restrictTo D.shading
        (sourceTauCover D C S m).activeFine).shading.shadingMass ≠ 0) :
    (sourceTauCover D C S m).activeFine.Nonempty := by
  by_contra hnot
  have hempty : (sourceTauCover D C S m).activeFine = ∅ :=
    Finset.not_nonempty_iff_eq_empty.mp hnot
  apply hsource
  rw [shadingMass_restrictTo_eq_sum, hempty]
  simp

/-- The source global Katz--Tao hypothesis restricts losslessly to the
literal active fine set of the source-to-`tau` cover. -/
theorem sourceTauCover_activeFine_isKatzTaoOn
    (D : ActualTubeDatum sourceDelta sourceIndex)
    (C : CoherentStickyMultiscaleCover D.family)
    (S : FiniteScaleSequence sourceDelta depth) (m : Fin depth)
    {eta : Real} (hKT : KatzTaoHypotheses D eta) :
    IsKatzTaoOn ((sourceDelta : ENNReal) ^ (-eta))
      D.family.bodyFamily (sourceTauCover D C S m).activeFine := by
  exact ((katzTaoHypotheses_iff_density_and_isKatzTao D eta).mp hKT).2.on _

/-- Canonical source-to-`tau` specialization of the real exact-card joint
factorization.  Besides the exact Eq.(45)-times-Eq.(46) count identity, the
same selected partition produces an actual exact assembly for every shading
on its selected fine family. -/
theorem exists_sourceTau_jointExactUniform_partition_and_assembly
    (D : ActualTubeDatum sourceDelta sourceIndex) (hD : D.IsAdmissible)
    (C : CoherentStickyMultiscaleCover D.family)
    (S : FiniteScaleSequence sourceDelta depth) (m : Fin depth)
    (htauHalf : S.tau m ≤ (2 : NNReal)⁻¹)
    (hsource :
      (IndexedShadingRefinement.restrictTo D.shading
        (sourceTauCover D C S m).activeFine).shading.shadingMass ≠ 0)
    {eta : Real} (hKT : KatzTaoHypotheses D eta)
    {a b : NNReal} {CF : ENNReal} {epsilon beta : Real}
    (ha : 0 < a) (hb : 0 < b)
    (hbeta : 0 ≤ beta) (hbetaOne : beta ≤ 1) :
    let S0 := sourceTauCover D C S m
    ∃ (level : Fin (Fintype.card sourceIndex + 1))
        (selected : Finset (Fin S0.coarseCard))
        (selectedFine : Finset sourceIndex)
        (fine' : UniformTubeFamily sourceDelta sourceIndex)
        (coarse' : UniformTubeFamily (S.tau m) (Fin S0.coarseCard))
        (P : CoarseTubePartition fine' coarse'),
      (∀ i, fine'.tubes i = D.family.tubes i) ∧
      (∀ k, coarse'.tubes k = S0.coarse.tubes k) ∧
      P.index = selectedIndexFactorization S0.activeFine S0.parent selected ∧
      P.branching = level.1 ∧ P.branchingLoss = 1 ∧
      WithinFactor (2 * (Fintype.card sourceIndex + 1))
        (bodyMassOn D.family.bodyFamily S0.activeFine)
        (bodyMassOn fine'.bodyFamily P.fineIndices) ∧
      selectedFine.Nonempty ∧ selected.Nonempty ∧
      selectedFine ⊆ S0.activeFine ∧ selected ⊆ S0.activeCoarse ∧
      (∀ k ∈ P.coarseIndices, (P.fiber k).card = level.1) ∧
      IsKatzTaoOn
        (2 * stickyJointScaleCoverLoss
          ((sourceDelta : ENNReal) ^ (-eta)) sourceDelta (S.tau m))
        coarse'.bodyFamily P.coarseIndices ∧
      (∀ k ∈ P.coarseIndices,
        IsFrostmanOn
          (2 * stickyJointScaleCoverLoss
            ((sourceDelta : ENNReal) ^ (-eta)) sourceDelta (S.tau m))
          fine'.bodyFamily (P.fiber k) (coarse'.bodyFamily k)) ∧
      proposition66AOuterFactor sourceDelta a b P.coarseIndices.card
            CF epsilon beta *
          proposition66AInnerFactor sourceDelta a b P.branching epsilon beta =
        proposition66AFrostmanFactor sourceDelta a b P.fineIndices.card
          CF epsilon beta ∧
      (∀ Y' : Shading fine'.bodyFamily,
        ∃ A : ExactAssembly P.asConvexFactorization Y'
            (((P.branching + 1) * (P.branching + 1)) *
              (Fintype.card (Fin S0.coarseCard) + 1)),
          A.fineLevel ≤ P.branching ∧
          A.outerLevel ≤ Fintype.card (Fin S0.coarseCard)) := by
  dsimp only
  have htauPos : 0 < S.tau m :=
    hD.delta_pos.trans_le (S.delta_le_tau m)
  have hA0 : (sourceDelta : ENNReal) ^ (-eta) ≠ 0 :=
    (ENNReal.rpow_pos (ENNReal.coe_pos.mpr hD.delta_pos)
      ENNReal.coe_ne_top).ne'
  have hAtop : (sourceDelta : ENNReal) ^ (-eta) ≠ ∞ :=
    ENNReal.rpow_ne_top_of_ne_zero
      (ENNReal.coe_ne_zero.mpr hD.delta_pos.ne') ENNReal.coe_ne_top
  obtain ⟨level, selected, selectedFine, fine', coarse', P,
      hfineTubes, hcoarseTubes, hindex, hbranching, hloss,
      hretain, hselectedFineNonempty, hselectedNonempty,
      hselectedFineSub, hselectedSub, hfiber, hcoarseKT,
      hfiberFrostman, hproduct⟩ :=
    exists_sticky_jointExactUniform_prop66A_product
      (sourceTauCover D C S m) hD.delta_pos htauPos
      (S.delta_le_tau m) hD.delta_le_half htauHalf
      (sourceTauCover_activeFine_nonempty_of_restrictedMass_ne_zero
        D C S m hsource)
      ((sourceDelta : ENNReal) ^ (-eta)) hA0 hAtop
      (sourceTauCover_activeFine_isKatzTaoOn D C S m hKT)
      ha hb hbeta hbetaOne
  refine ⟨level, selected, selectedFine, fine', coarse', P,
    hfineTubes, hcoarseTubes, hindex, hbranching, hloss,
    hretain, hselectedFineNonempty, hselectedNonempty,
    hselectedFineSub, hselectedSub, hfiber, hcoarseKT,
    hfiberFrostman, hproduct, ?_⟩
  intro Y'
  exact exists_exactAssembly_of_branchingLoss_eq_one P Y' hloss

#print axioms exists_exactAssembly_of_branchingLoss_eq_one
#print axioms sourceTauCover_activeFine_nonempty_of_restrictedMass_ne_zero
#print axioms sourceTauCover_activeFine_isKatzTaoOn
#print axioms exists_sourceTau_jointExactUniform_partition_and_assembly

end
end Family8SourceTauJointExactUniformProducerV1
