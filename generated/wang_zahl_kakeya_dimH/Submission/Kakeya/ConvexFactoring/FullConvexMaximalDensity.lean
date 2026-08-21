import Submission.Kakeya.ConvexGeometry.Family
import Submission.Kakeya.ConvexFactoring.MaximalDensity
import Submission.Kakeya.ConvexFactoring.FiniteCandidateFactoring

open scoped ENNReal NNReal
open MeasureTheory

namespace Submission.Kakeya.ConvexFactoring

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry

noncomputable section

/-!
# Full convex-container maximal density

For a finite active family, the candidate list consists of the closed convex
hulls of all its nonempty subfamilies.  Given any `ConvexBody`, the hull of the
active members contained in it is itself a candidate and is contained in the
original body.  Consequently, a finite-candidate winner is globally maximal
against every convex body, not merely against the enumerated candidates.
-/

namespace FullConvexMaximalDensity

/-- Union of the bodies selected by the finite index set `s`. -/
def selectedUnion {ι : Type*} (F : ConvexFamily ι) (s : Finset ι) : Set Space :=
  ⋃ i : {i // i ∈ s}, (F i.1 : Set Space)

theorem selectedUnion_isCompact {ι : Type*} (F : ConvexFamily ι) (s : Finset ι) :
    IsCompact (selectedUnion F s) := by
  exact isCompact_iUnion fun i : {i // i ∈ s} ↦ (F i.1).isCompact

theorem body_subset_selectedUnion {ι : Type*} (F : ConvexFamily ι)
    {s : Finset ι} {i : ι} (hi : i ∈ s) :
    (F i : Set Space) ⊆ selectedUnion F s := by
  intro x hx
  exact Set.mem_iUnion.mpr ⟨⟨i, hi⟩, hx⟩

theorem selectedUnion_nonempty {ι : Type*} (F : ConvexFamily ι)
    {s : Finset ι} (hs : s.Nonempty) :
    (selectedUnion F s).Nonempty := by
  obtain ⟨i, hi⟩ := hs
  exact (F i).nonempty.mono (body_subset_selectedUnion F hi)

theorem closedConvexHull_selectedUnion_isCompact {ι : Type*}
    (F : ConvexFamily ι) (s : Finset ι) :
    IsCompact (closedConvexHull ℝ (selectedUnion F s)) := by
  rw [closedConvexHull_eq_closure_convexHull]
  exact (selectedUnion_isCompact F s).totallyBounded.convexHull.isBounded.isCompact_closure

/-- An explicit singleton convex body, used only for the empty subfamily. -/
def singletonBody (x : Space) : ConvexBody Space where
  carrier := {x}
  convex' := convex_singleton x
  isCompact' := isCompact_singleton
  nonempty' := Set.singleton_nonempty x

@[simp] theorem coe_singletonBody (x : Space) :
    (singletonBody x : Set Space) = {x} :=
  rfl

/-- The compact closed convex hull associated to a nonempty subfamily. -/
def nonemptyHullContainer {ι : Type*} (F : ConvexFamily ι)
    (s : Finset ι) (hs : s.Nonempty) : ConvexBody Space where
  carrier := closedConvexHull ℝ (selectedUnion F s)
  convex' := convex_closedConvexHull
  isCompact' := closedConvexHull_selectedUnion_isCompact F s
  nonempty' :=
    (selectedUnion_nonempty F hs).mono subset_closedConvexHull

/-- Closed-convex-hull candidate for `s`; the empty set is represented by the
explicit singleton body `{0}`. -/
def hullContainer {ι : Type*} (F : ConvexFamily ι)
    (s : Finset ι) : ConvexBody Space :=
  if hs : s.Nonempty then nonemptyHullContainer F s hs else singletonBody 0

@[simp] theorem coe_hullContainer_of_nonempty {ι : Type*}
    (F : ConvexFamily ι) {s : Finset ι} (hs : s.Nonempty) :
    (hullContainer F s : Set Space) = closedConvexHull ℝ (selectedUnion F s) := by
  simp [hullContainer, hs, nonemptyHullContainer]

@[simp] theorem coe_hullContainer_empty {ι : Type*} (F : ConvexFamily ι) :
    (hullContainer F ∅ : Set Space) = {0} := by
  simp [hullContainer]

theorem body_subset_hullContainer {ι : Type*} (F : ConvexFamily ι)
    {s : Finset ι} {i : ι} (hi : i ∈ s) (hs : s.Nonempty) :
    (F i : Set Space) ⊆ (hullContainer F s : Set Space) := by
  rw [coe_hullContainer_of_nonempty F hs]
  exact (body_subset_selectedUnion F hi).trans subset_closedConvexHull

theorem hullContainer_subset {ι : Type*} (F : ConvexFamily ι)
    {s : Finset ι} {K : ConvexBody Space} (hs : s.Nonempty)
    (hsub : ∀ i ∈ s, (F i : Set Space) ⊆ (K : Set Space)) :
    (hullContainer F s : Set Space) ⊆ (K : Set Space) := by
  rw [coe_hullContainer_of_nonempty F hs]
  apply closedConvexHull_min _ K.convex K.isClosed
  intro x hx
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
  exact hsub i i.property hi

/-- All nonempty finite subsets of `active`, viewed as a finite candidate set. -/
def hullCandidates {ι : Type*} (active : Finset ι) : Finset (Finset ι) :=
  active.powerset.filter Finset.Nonempty

@[simp] theorem mem_hullCandidates {ι : Type*} {active s : Finset ι} :
    s ∈ hullCandidates active ↔ s ⊆ active ∧ s.Nonempty := by
  simp [hullCandidates]

theorem hullCandidates_nonempty {ι : Type*} {active : Finset ι}
    (hactive : active.Nonempty) : (hullCandidates active).Nonempty := by
  obtain ⟨i, hi⟩ := hactive
  refine ⟨{i}, ?_⟩
  simp [hi]

theorem hullCandidates_cover {ι : Type*} (F : ConvexFamily ι)
    {active : Finset ι} {i : ι} (hi : i ∈ active) :
    ∃ s ∈ hullCandidates active,
      (F i : Set Space) ⊆ (hullContainer F s : Set Space) := by
  refine ⟨{i}, ?_, body_subset_hullContainer F (by simp) (by simp)⟩
  simp [hi]

theorem hullContainer_indicesInside_subset
    {ι : Type*} [Fintype ι] (F : ConvexFamily ι)
    (active : Finset ι) (K : ConvexBody Space)
    (hs : (indicesInside F active K).Nonempty) :
    (hullContainer F (indicesInside F active K) : Set Space) ⊆ (K : Set Space) := by
  apply hullContainer_subset F hs
  intro i hi
  exact (mem_indicesInside F active K i).1 hi |>.2

theorem indicesInside_hullContainer_indicesInside_eq
    {ι : Type*} [Fintype ι] (F : ConvexFamily ι)
    (active : Finset ι) (K : ConvexBody Space)
    (hs : (indicesInside F active K).Nonempty) :
    indicesInside F active (hullContainer F (indicesInside F active K)) =
      indicesInside F active K := by
  classical
  have hsub := hullContainer_indicesInside_subset F active K hs
  ext i
  rw [mem_indicesInside, mem_indicesInside]
  constructor
  · rintro ⟨hiActive, hiHull⟩
    exact ⟨hiActive, hiHull.trans hsub⟩
  · intro hi
    have hiIndices : i ∈ indicesInside F active K :=
      (mem_indicesInside F active K i).2 hi
    exact ⟨hi.1, body_subset_hullContainer F hiIndices hs⟩

theorem massInside_hullContainer_indicesInside_eq
    {ι : Type*} [Fintype ι] (F : ConvexFamily ι)
    (active : Finset ι) (K : ConvexBody Space)
    (hs : (indicesInside F active K).Nonempty) :
    massInside F active (hullContainer F (indicesInside F active K)) =
      massInside F active K := by
  unfold massInside
  rw [indicesInside_hullContainer_indicesInside_eq F active K hs]

/-- If some active body lies in `K`, the hull of exactly all active bodies in
`K` has at least the active density of `K`. -/
theorem densityInside_le_hullContainer_indicesInside
    {ι : Type*} [Fintype ι] (F : ConvexFamily ι)
    (active : Finset ι) (K : ConvexBody Space)
    (hs : (indicesInside F active K).Nonempty) :
    densityInside F active K ≤
      densityInside F active (hullContainer F (indicesInside F active K)) := by
  unfold densityInside
  rw [massInside_hullContainer_indicesInside_eq F active K hs]
  exact ENNReal.div_le_div_left
    (measure_mono (hullContainer_indicesInside_subset F active K hs)) _

/-- Every convex body is density-dominated by one of the hull candidates from
`base`, provided the current active set is contained in `base`.  If no active
body lies in `K`, its density is zero and any singleton candidate suffices. -/
theorem exists_hullCandidate_density_ge
    {ι : Type*} [Fintype ι] (F : ConvexFamily ι)
    {base active : Finset ι} (hbase : base.Nonempty) (hactive : active ⊆ base)
    (K : ConvexBody Space) :
    ∃ s ∈ hullCandidates base,
      densityInside F active K ≤ densityInside F active (hullContainer F s) := by
  classical
  by_cases hempty : indicesInside F active K = ∅
  · obtain ⟨i, hi⟩ := hbase
    refine ⟨{i}, ?_, ?_⟩
    · simp [hi]
    · rw [densityInside_eq_zero_of_indicesInside_eq_empty F active K hempty]
      exact bot_le
  · have hs : (indicesInside F active K).Nonempty :=
      Finset.nonempty_iff_ne_empty.mpr hempty
    refine ⟨indicesInside F active K, ?_,
      densityInside_le_hullContainer_indicesInside F active K hs⟩
    rw [mem_hullCandidates]
    exact ⟨(indicesInside_subset F active K).trans hactive, hs⟩

/-- A finite hull-candidate maximizer is automatically maximal against every
convex body, not merely against the enumerated candidates. -/
theorem maximalDensityChoice_density_ge_all
    {ι : Type*} [Fintype ι] {F : ConvexFamily ι}
    {base active : Finset ι}
    (M : MaximalDensityChoice F active (hullCandidates base) (hullContainer F))
    (hbase : base.Nonempty) (hactive : active ⊆ base)
    (K : ConvexBody Space) :
    densityInside F active K ≤
      densityInside F active (hullContainer F M.index) := by
  obtain ⟨s, hs, hle⟩ :=
    exists_hullCandidate_density_ge F hbase hactive K
  exact hle.trans (M.maximal s hs)

/-- For a nonempty active set there exists a finite hull-candidate choice whose
density is globally maximal over all convex bodies. -/
theorem exists_globalMaximalDensityChoice
    {ι : Type*} [Fintype ι] (F : ConvexFamily ι) (active : Finset ι)
    (hactive : active.Nonempty) :
    ∃ M : MaximalDensityChoice F active (hullCandidates active) (hullContainer F),
      ∀ K : ConvexBody Space,
        densityInside F active K ≤
          densityInside F active (hullContainer F M.index) := by
  classical
  obtain ⟨M⟩ := exists_maximalDensityChoice F active
    (hullCandidates active) (hullContainer F) (hullCandidates_nonempty hactive)
  exact ⟨M, fun K ↦ maximalDensityChoice_density_ge_all M hactive (fun _ h ↦ h) K⟩

/-- The winner's captured mass agrees with the active mass in its container. -/
theorem hullChoice_fiber_massInside_self_eq
    {ι : Type*} [Fintype ι] {F : ConvexFamily ι}
    {base active : Finset ι}
    (M : MaximalDensityChoice F active (hullCandidates base) (hullContainer F)) :
    massInside F M.fiber (hullContainer F M.index) =
      massInside F active (hullContainer F M.index) := by
  classical
  have hindices :
      indicesInside F M.fiber (hullContainer F M.index) = M.fiber := by
    ext i
    rw [mem_indicesInside]
    constructor
    · exact fun hi ↦ hi.1
    · intro hi
      exact ⟨hi, M.body_subset_container hi⟩
  unfold massInside
  rw [hindices]
  rfl

/-- The winning fiber's density in every convex body is bounded by the
winning active density. -/
theorem hullChoice_fiber_density_le_all
    {ι : Type*} [Fintype ι] {F : ConvexFamily ι}
    {base active : Finset ι}
    (M : MaximalDensityChoice F active (hullCandidates base) (hullContainer F))
    (hbase : base.Nonempty) (hactive : active ⊆ base)
    (K : ConvexBody Space) :
    densityInside F M.fiber K ≤
      densityInside F active (hullContainer F M.index) :=
  (densityInside_mono F M.fiber_subset K).trans
    (maximalDensityChoice_density_ge_all M hbase hactive K)

/-- Denominator-cleared mass bound for the winning fiber in an arbitrary
convex body.  The zero-volume case is handled without cancellation. -/
theorem hullChoice_fiber_massInside_le_all
    {ι : Type*} [Fintype ι] {F : ConvexFamily ι}
    {base active : Finset ι}
    (M : MaximalDensityChoice F active (hullCandidates base) (hullContainer F))
    (hbase : base.Nonempty) (hactive : active ⊆ base)
    (K : ConvexBody Space) :
    massInside F M.fiber K ≤
      densityInside F active (hullContainer F M.index) * volume (K : Set Space) := by
  by_cases hzero : volume (K : Set Space) = 0
  · rw [massInside_eq_zero_of_volume_eq_zero F M.fiber K hzero,
      hzero, mul_zero]
  · exact (ENNReal.div_le_iff_le_mul
      (Or.inl hzero) (Or.inl K.isCompact.measure_lt_top.ne)).1
        (hullChoice_fiber_density_le_all M hbase hactive K)

/-- Global zero-volume-safe Frostman cross inequality for the actual winning
fiber, against every convex body `K`. -/
theorem hullChoice_fiber_frostmanCross_le_all
    {ι : Type*} [Fintype ι] {F : ConvexFamily ι}
    {base active : Finset ι}
    (M : MaximalDensityChoice F active (hullCandidates base) (hullContainer F))
    (hbase : base.Nonempty) (hactive : active ⊆ base)
    (K : ConvexBody Space) :
    massInside F M.fiber K * volume (hullContainer F M.index : Set Space) ≤
      massInside F M.fiber (hullContainer F M.index) * volume (K : Set Space) := by
  rw [hullChoice_fiber_massInside_self_eq M]
  by_cases hwin : volume (hullContainer F M.index : Set Space) = 0
  · simp [hwin]
  · calc
      massInside F M.fiber K * volume (hullContainer F M.index : Set Space) ≤
          (densityInside F active (hullContainer F M.index) *
            volume (K : Set Space)) *
              volume (hullContainer F M.index : Set Space) := by
            gcongr
            exact hullChoice_fiber_massInside_le_all M hbase hactive K
      _ = (densityInside F active (hullContainer F M.index) *
            volume (hullContainer F M.index : Set Space)) *
              volume (K : Set Space) := by
            ac_rfl
      _ = massInside F active (hullContainer F M.index) *
              volume (K : Set Space) := by
            rw [densityInside, ENNReal.div_mul_cancel hwin
              (hullContainer F M.index).isCompact.measure_lt_top.ne]

/-- Every greedy step satisfies the global cross inequality against every
convex body, rather than only against finite candidates. -/
def AllWinnerGlobalCross
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (F : ConvexFamily ι) (base : Finset ι) :
    {s : Finset ι} →
      GreedyDensityPartition F (hullCandidates base) (hullContainer F) s → Prop
  | _, .empty => True
  | _, .step choice _ tail =>
      (∀ K : ConvexBody Space,
        massInside F choice.fiber K *
            volume (hullContainer F choice.index : Set Space) ≤
          massInside F choice.fiber (hullContainer F choice.index) *
            volume (K : Set Space)) ∧
      AllWinnerGlobalCross F base tail

theorem allWinnerGlobalCross_of_subset
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (F : ConvexFamily ι) (base : Finset ι) :
    ∀ {active : Finset ι}
      (P : GreedyDensityPartition F (hullCandidates base) (hullContainer F) active),
      active ⊆ base → AllWinnerGlobalCross F base P
  | _, .empty, _ => trivial
  | _, .step choice hfiber tail, hactive => by
      have hcurrent : _ := hfiber.mono choice.fiber_subset
      have hbase : base.Nonempty := hcurrent.mono hactive
      exact ⟨fun K ↦ hullChoice_fiber_frostmanCross_le_all
          choice hbase hactive K,
        allWinnerGlobalCross_of_subset F base tail
          (Finset.sdiff_subset.trans hactive)⟩

/-- The hull candidates yield a terminating greedy partition with exact
coverage, the usual step bound, and a global cross inequality at every step. -/
theorem exists_fullConvexGreedyDensityPartition
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (F : ConvexFamily ι) (active : Finset ι) :
    ∃ P : GreedyDensityPartition F (hullCandidates active) (hullContainer F) active,
      P.coveredIndices = active ∧
      P.length ≤ active.card ∧
      AllWinnerGlobalCross F active P := by
  classical
  have hcover : ∀ i ∈ active, ∃ s ∈ hullCandidates active,
      (F i : Set Space) ⊆ (hullContainer F s : Set Space) := by
    intro i hi
    exact hullCandidates_cover F hi
  obtain ⟨P⟩ := exists_greedyDensityPartition F active
    (hullCandidates active) (hullContainer F) hcover
  exact ⟨P, P.coveredIndices_eq, P.length_le_card,
    allWinnerGlobalCross_of_subset F active P (fun _ h ↦ h)⟩

end FullConvexMaximalDensity

end

end Submission.Kakeya.ConvexFactoring
