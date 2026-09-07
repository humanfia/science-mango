import Family8Grounding.Family8NormalizedCFDividingWitnessBridgeV2
import Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
import Mathlib.Tactic

/-!
# A genuine hull choice at one prescribed active parent, V2

This is the parent-local counterpart of the global `CFMaxHullChoice`.  The
parent is supplied by the caller (for example, the mass-popular parent), so
no claim is made that it attains the cover-wide supremum.  A lower bound for
that parent's own normalized Frostman constant is converted into the exact
same-parent hull-density inequality.  V1 misspelled one open namespace and
is not imported.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8StickyScaleCoverSelectedParentCFAtHullChoiceV2

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

variable {delta rho : NNReal} {iota : Type*}
  [Fintype iota] [DecidableEq iota]
  {fine : UniformTubeFamily delta iota}

/-- A nonempty full-convex density maximizer in the literal fibre of the
prescribed active parent. -/
structure SelectedParentCFAtHullChoice
    (S : StickyScaleCover fine rho)
    (parent : {k // k ∈ S.activeCoarse}) where
  choice : MaximalDensityChoice (S.fiberFamily parent.1) Finset.univ
    (hullCandidates
      (Finset.univ : Finset {i // i ∈ S.fiber parent.1}))
    (hullContainer (S.fiberFamily parent.1))
  choice_fiber_nonempty : choice.fiber.Nonempty
  choice_global : ∀ K : ConvexBody Space,
    densityInside (S.fiberFamily parent.1) Finset.univ K ≤
      densityInside (S.fiberFamily parent.1) Finset.univ
        (hullContainer (S.fiberFamily parent.1) choice.index)

namespace SelectedParentCFAtHullChoice

variable {S : StickyScaleCover fine rho}
  {parent : {k // k ∈ S.activeCoarse}}

/-- The winning full-convex hull inside the prescribed parent's fibre. -/
abbrev hull (Q : SelectedParentCFAtHullChoice S parent) : ConvexBody Space :=
  hullContainer (S.fiberFamily parent.1) Q.choice.index

/-- The selected hull realizes the maximal concentration of this prescribed
parent's full fibre. -/
theorem maximalConcentration_eq_winnerDensity
    (Q : SelectedParentCFAtHullChoice S parent) :
    maximalConcentration (S.fiberFamily parent.1) =
      densityInside (S.fiberFamily parent.1) Finset.univ Q.hull := by
  apply le_antisymm
  · apply iSup_le
    intro K
    rw [← densityInside_univ_eq_concentration]
    exact Q.choice_global K
  · rw [densityInside_univ_eq_concentration]
    exact concentration_le_maximalConcentration
      (S.fiberFamily parent.1) Q.hull

/-- Exact normalized constant at the prescribed parent in terms of its
winning hull density. -/
theorem parentNormalizedFiberCFAt_eq_winnerDensity
    (Q : SelectedParentCFAtHullChoice S parent) :
    parentNormalizedFiberCFAt S parent =
      densityInside (S.fiberFamily parent.1) Finset.univ Q.hull *
          volume (S.activeCoarseFamily parent : Set Space) /
        familyVolume (S.fiberFamily parent.1) := by
  unfold parentNormalizedFiberCFAt canonicalFrostmanConstant
  rw [Q.maximalConcentration_eq_winnerDensity,
    containedMass_fiberFamily_parent_eq_familyVolume]

/-- A high-CF hypothesis at the actual selected parent gives the honest
same-parent, same-hull mass inequality; no cover-wide maximizer is used. -/
theorem lower_mul_fiberVolume_le_winnerDensity_mul_parentVolume
    (Q : SelectedParentCFAtHullChoice S parent) (hdelta : 0 < delta)
    {lower : ENNReal} (hlower : lower ≤ parentNormalizedFiberCFAt S parent) :
    lower * familyVolume (S.fiberFamily parent.1) ≤
      densityInside (S.fiberFamily parent.1) Finset.univ Q.hull *
        volume (S.activeCoarseFamily parent : Set Space) := by
  have hmass0 : familyVolume (S.fiberFamily parent.1) ≠ 0 :=
    (fiberFamilyVolume_pos S hdelta parent).ne'
  have hmassTop : familyVolume (S.fiberFamily parent.1) ≠ ∞ :=
    familyVolume_ne_top (S.fiberFamily parent.1)
  have hnormalized : lower ≤
      densityInside (S.fiberFamily parent.1) Finset.univ Q.hull *
          volume (S.activeCoarseFamily parent : Set Space) /
        familyVolume (S.fiberFamily parent.1) := by
    rw [← Q.parentNormalizedFiberCFAt_eq_winnerDensity]
    exact hlower
  exact (ENNReal.le_div_iff_mul_le
    (Or.inl hmass0) (Or.inl hmassTop)).1 hnormalized

end SelectedParentCFAtHullChoice

/-- Every actual active parent admits the local full-convex hull choice. -/
theorem selectedParentCFAtHullChoice_nonempty
    (S : StickyScaleCover fine rho)
    (parent : {k // k ∈ S.activeCoarse}) :
    Nonempty (SelectedParentCFAtHullChoice S parent) := by
  classical
  obtain ⟨i, hiActive, hiParent⟩ :=
    S.parent_surjective parent.1 parent.2
  have hiFiber : i ∈ S.fiber parent.1 :=
    (S.mem_fiber i parent.1).2 ⟨hiActive, hiParent⟩
  have hfiberUniv :
      (Finset.univ : Finset {i // i ∈ S.fiber parent.1}).Nonempty :=
    ⟨⟨i, hiFiber⟩, Finset.mem_univ _⟩
  obtain ⟨M, hMfiber⟩ :=
    exists_maximalDensityChoice_fiber_nonempty
      (S.fiberFamily parent.1)
      (Finset.univ : Finset {i // i ∈ S.fiber parent.1})
      (hullCandidates
        (Finset.univ : Finset {i // i ∈ S.fiber parent.1}))
      (hullContainer (S.fiberFamily parent.1)) hfiberUniv
      (fun j _hj ↦ hullCandidates_cover
        (S.fiberFamily parent.1) (Finset.mem_univ j))
  exact ⟨{
    choice := M
    choice_fiber_nonempty := hMfiber
    choice_global := fun K ↦
      maximalDensityChoice_density_ge_all M hfiberUniv
        (fun _ hj ↦ hj) K }⟩

#print axioms SelectedParentCFAtHullChoice
#print axioms SelectedParentCFAtHullChoice.maximalConcentration_eq_winnerDensity
#print axioms SelectedParentCFAtHullChoice.parentNormalizedFiberCFAt_eq_winnerDensity
#print axioms
  SelectedParentCFAtHullChoice.lower_mul_fiberVolume_le_winnerDensity_mul_parentVolume
#print axioms selectedParentCFAtHullChoice_nonempty

end
end Family8StickyScaleCoverSelectedParentCFAtHullChoiceV2
