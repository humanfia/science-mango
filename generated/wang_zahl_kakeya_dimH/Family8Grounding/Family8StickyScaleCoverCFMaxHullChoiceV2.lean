import Family8Grounding.Family8NormalizedCFDividingWitnessBridgeV2
import Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8StickyScaleCoverCFMaxHullChoiceV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.Uniformity
open Family6CanonicalFrostmanConstantCoreV1
open Family8GreedyOccurrenceCanonicalFrostmanBridgeV2
open Family8NormalizedCFDividingWitnessBridgeV2.StickyScaleCover
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

/-!
# A genuine same-parent witness for the worst normalized fibre constant

The outer supremum in `parentNormalizedFiberCFMax` is finite, so one literal
active parent attains it.  Within that parent's literal fibre, the finite
full-convex hull catalogue contains a nonempty choice whose density dominates
every convex test body.  The record below keeps these two choices tied to the
same parent.

This is extraction data, not a desired multiplicity estimate.  Its final
projection is the honest cross-multiplied consequence of a lower `C_F`
barrier and can be used to build a successor datum inside the winning hull.
-/

variable {delta rho : NNReal} {iota : Type*}
  [Fintype iota] [DecidableEq iota]
  {fine : UniformTubeFamily delta iota}

/-- One literal active parent attaining the cover's normalized `C_F` maximum,
together with a nonempty full-convex hull choice attaining the maximal
concentration of that very same parent fibre. -/
structure CFMaxHullChoice (S : StickyScaleCover fine rho) where
  parent : {k // k ∈ S.activeCoarse}
  choice : MaximalDensityChoice (S.fiberFamily parent.1) Finset.univ
    (hullCandidates
      (Finset.univ : Finset {i // i ∈ S.fiber parent.1}))
    (hullContainer (S.fiberFamily parent.1))
  choice_fiber_nonempty : choice.fiber.Nonempty
  parent_attains :
    parentNormalizedFiberCFMax S = parentNormalizedFiberCFAt S parent
  choice_global : ∀ K : ConvexBody Space,
    densityInside (S.fiberFamily parent.1) Finset.univ K ≤
      densityInside (S.fiberFamily parent.1) Finset.univ
        (hullContainer (S.fiberFamily parent.1) choice.index)

namespace CFMaxHullChoice

variable {S : StickyScaleCover fine rho}

/-- The winning full-convex hull. -/
abbrev hull (Q : CFMaxHullChoice S) : ConvexBody Space :=
  hullContainer (S.fiberFamily Q.parent.1) Q.choice.index

/-- The selected fine members are a literal nonempty subset of the fibre of
the same parent stored by the choice. -/
theorem selected_subset_parentFiber (Q : CFMaxHullChoice S) :
    Q.choice.fiber ⊆ Finset.univ :=
  Q.choice.fiber_subset

/-- The selected hull realizes the maximal concentration of the chosen
parent's literal fibre. -/
theorem maximalConcentration_eq_winnerDensity (Q : CFMaxHullChoice S) :
    maximalConcentration (S.fiberFamily Q.parent.1) =
      densityInside (S.fiberFamily Q.parent.1) Finset.univ Q.hull := by
  apply le_antisymm
  · apply iSup_le
    intro K
    rw [← densityInside_univ_eq_concentration]
    exact Q.choice_global K
  · rw [densityInside_univ_eq_concentration]
    exact concentration_le_maximalConcentration
      (S.fiberFamily Q.parent.1) Q.hull

/-- The exact normalized scalar at the chosen parent is the winning hull
density times parent volume, divided by the full fibre mass. -/
theorem parentNormalizedFiberCFAt_eq_winnerDensity (Q : CFMaxHullChoice S) :
    parentNormalizedFiberCFAt S Q.parent =
      densityInside (S.fiberFamily Q.parent.1) Finset.univ Q.hull *
          volume (S.activeCoarseFamily Q.parent : Set Space) /
        familyVolume (S.fiberFamily Q.parent.1) := by
  unfold parentNormalizedFiberCFAt canonicalFrostmanConstant
  rw [Q.maximalConcentration_eq_winnerDensity,
    containedMass_fiberFamily_parent_eq_familyVolume]

/-- A lower normalized `C_F` barrier becomes an honest same-parent,
same-hull mass inequality. -/
theorem lower_mul_fiberVolume_le_winnerDensity_mul_parentVolume
    (Q : CFMaxHullChoice S) (hdelta : 0 < delta)
    {lower : ENNReal} (hlower : lower ≤ parentNormalizedFiberCFMax S) :
    lower * familyVolume (S.fiberFamily Q.parent.1) ≤
      densityInside (S.fiberFamily Q.parent.1) Finset.univ Q.hull *
        volume (S.activeCoarseFamily Q.parent : Set Space) := by
  have hmass0 : familyVolume (S.fiberFamily Q.parent.1) ≠ 0 :=
    (fiberFamilyVolume_pos S hdelta Q.parent).ne'
  have hmassTop : familyVolume (S.fiberFamily Q.parent.1) ≠ ∞ :=
    familyVolume_ne_top (S.fiberFamily Q.parent.1)
  have hnormalized : lower ≤
      densityInside (S.fiberFamily Q.parent.1) Finset.univ Q.hull *
          volume (S.activeCoarseFamily Q.parent : Set Space) /
        familyVolume (S.fiberFamily Q.parent.1) := by
    rw [← Q.parentNormalizedFiberCFAt_eq_winnerDensity,
      ← Q.parent_attains]
    exact hlower
  exact (ENNReal.le_div_iff_mul_le
    (Or.inl hmass0) (Or.inl hmassTop)).1 hnormalized

end CFMaxHullChoice

/-- Every cover with one active parent has a compact same-parent `C_F` hull
choice.  No concentration, Frostman, or desired-bound premise is supplied. -/
theorem cfMaxHullChoice_nonempty
    (S : StickyScaleCover fine rho) (hactive : S.activeCoarse.Nonempty) :
    Nonempty (CFMaxHullChoice S) := by
  classical
  have hparentUniv :
      (Finset.univ : Finset {k // k ∈ S.activeCoarse}).Nonempty := by
    obtain ⟨k, hk⟩ := hactive
    exact ⟨⟨k, hk⟩, Finset.mem_univ _⟩
  obtain ⟨k, _hkUniv, hkMax⟩ :=
    Finset.exists_mem_eq_sup
      (Finset.univ : Finset {k // k ∈ S.activeCoarse}) hparentUniv
      (parentNormalizedFiberCFAt S)
  have hparentAttains :
      parentNormalizedFiberCFMax S = parentNormalizedFiberCFAt S k := by
    rw [parentNormalizedFiberCFMax, ← Finset.sup_univ_eq_iSup]
    exact hkMax
  obtain ⟨i, hiActive, hiParent⟩ :=
    S.parent_surjective k.1 k.2
  have hiFiber : i ∈ S.fiber k.1 :=
    (S.mem_fiber i k.1).2 ⟨hiActive, hiParent⟩
  have hfiberUniv :
      (Finset.univ : Finset {i // i ∈ S.fiber k.1}).Nonempty :=
    ⟨⟨i, hiFiber⟩, Finset.mem_univ _⟩
  obtain ⟨M, hMfiber⟩ :=
    exists_maximalDensityChoice_fiber_nonempty
      (S.fiberFamily k.1)
      (Finset.univ : Finset {i // i ∈ S.fiber k.1})
      (hullCandidates
        (Finset.univ : Finset {i // i ∈ S.fiber k.1}))
      (hullContainer (S.fiberFamily k.1)) hfiberUniv
      (fun j _hj ↦ hullCandidates_cover
        (S.fiberFamily k.1) (Finset.mem_univ j))
  refine ⟨{
    parent := k
    choice := M
    choice_fiber_nonempty := hMfiber
    parent_attains := hparentAttains
    choice_global := ?_ }⟩
  intro K
  exact maximalDensityChoice_density_ge_all M hfiberUniv
    (fun _ hj ↦ hj) K

#print axioms CFMaxHullChoice
#print axioms CFMaxHullChoice.maximalConcentration_eq_winnerDensity
#print axioms CFMaxHullChoice.parentNormalizedFiberCFAt_eq_winnerDensity
#print axioms
  CFMaxHullChoice.lower_mul_fiberVolume_le_winnerDensity_mul_parentVolume
#print axioms cfMaxHullChoice_nonempty

end
end Family8StickyScaleCoverCFMaxHullChoiceV2
