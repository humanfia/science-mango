import FamilyStickyGrounding.FamilyStickyScaleChainCoherentMassLocalizationProducerV1
import FamilyStickyGrounding.FamilyStickyDividingScalesChainAtEveryAdapterV1

set_option autoImplicit false
set_option warningAsError true

open Set
open scoped ENNReal NNReal

namespace FamilyStickyScaleChainArbitraryRadiusInterpolationV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDeltaMaxFiniteChainV2
open FamilyStickyDeltaMaxFiniteChainV2.StickyScaleCover
open FamilyStickyAdjacentScaleStepV2.StickyScaleCover
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainActualValuesV1
open FamilyStickyScaleChainCoherentIntervalProducerV1
open FamilyStickyScaleChainNestedMassLocalizationV1.StickyScaleCover
open FamilyStickyScaleChainCoherentMassLocalizationProducerV1

noncomputable section
set_option linter.unusedSectionVars false

/-!
# Arbitrary-radius interpolation from a finite sticky scale chain

A `StickyMultiscaleCover` chooses its cover independently at every radius.
Consequently endpoint estimates on a finite scale chain do not constrain an
intermediate cover.  The coherent-cover API supplies actual cross-scale
parents and carrier containment, but two further local facts are needed:

* a fine fiber at the intermediate radius is a subfamily of its endpoint
  fiber, together with comparison of the two parent-normalizing
  concentrations;
* the existing parent-mass and thickened-body estimates on the intermediate
  coarse family.

The companion bounds module records those facts only on one adjacent interval.
Its theorems locate an arbitrary radius in the finite chain and derive the full
Frostman and Katz--Tao statements without assuming either final at-every-scale
conclusion.
-/

/-! ## Canonical interval containing an arbitrary radius -/

namespace FiniteScaleSequence

variable {delta : NNReal} {depth : Nat}

/-- Scale nodes whose radius has already dropped below `rho`. -/
def belowNodes (S : FiniteScaleSequence delta depth) (rho : NNReal) :
    Finset (Fin (depth + 1)) :=
  Finset.univ.filter fun j => S.radius j <= rho

@[simp]
theorem mem_belowNodes (S : FiniteScaleSequence delta depth) (rho : NNReal)
    (j : Fin (depth + 1)) :
    j ∈ belowNodes S rho <-> S.radius j <= rho := by
  simp [belowNodes]

theorem belowNodes_nonempty (S : FiniteScaleSequence delta depth)
    (rho : NNReal) (hdelta : delta <= rho) :
    (belowNodes S rho).Nonempty := by
  refine ⟨Fin.last depth, ?_⟩
  rw [mem_belowNodes S, S.bottom_eq]
  exact hdelta

/-- The first chain node whose radius is at most `rho`. -/
def firstBelow (S : FiniteScaleSequence delta depth)
    (rho : NNReal) (hdelta : delta <= rho) : Fin (depth + 1) :=
  (belowNodes S rho).min' (belowNodes_nonempty S rho hdelta)

theorem firstBelow_mem (S : FiniteScaleSequence delta depth)
    (rho : NNReal) (hdelta : delta <= rho) :
    firstBelow S rho hdelta ∈ belowNodes S rho := by
  exact Finset.min'_mem _ _

theorem firstBelow_le (S : FiniteScaleSequence delta depth)
    (rho : NNReal) (hdelta : delta <= rho)
    (j : Fin (depth + 1)) (hj : S.radius j <= rho) :
    firstBelow S rho hdelta <= j := by
  exact Finset.min'_le _ _ ((mem_belowNodes S rho j).2 hj)

/-- The adjacent interval selected by the first node below `rho`.  At the top
endpoint, interval zero is used. -/
def nearestInterval (S : FiniteScaleSequence delta depth)
    (hdepth : 0 < depth) (rho : NNReal) (hdelta : delta <= rho) : Fin depth :=
  let j := firstBelow S rho hdelta
  if hj : j.1 = 0 then
    ⟨0, hdepth⟩
  else
    ⟨j.1 - 1, by
      have hjle : j.1 <= depth := Nat.le_of_lt_succ j.2
      have hjpos : 0 < j.1 := Nat.pos_of_ne_zero hj
      omega⟩

theorem tau_nearestInterval_le (S : FiniteScaleSequence delta depth)
    (hdepth : 0 < depth) (rho : NNReal)
    (hdelta : delta <= rho) (hrho : rho <= 1) :
    S.tau (nearestInterval S hdepth rho hdelta) <= rho := by
  let j := firstBelow S rho hdelta
  have hjmem : S.radius j <= rho :=
    (mem_belowNodes S rho j).1 (firstBelow_mem S rho hdelta)
  by_cases hjzero : j.1 = 0
  · have hj : j = (0 : Fin (depth + 1)) := Fin.ext hjzero
    have honeRho : 1 <= rho := by
      rw [← S.top_eq]
      simpa only [hj] using hjmem
    have hrhoOne : rho = 1 := le_antisymm hrho honeRho
    simp only [nearestInterval, j, dif_pos hjzero]
    change S.tau ⟨0, hdepth⟩ <= rho
    calc
      S.tau ⟨0, hdepth⟩ <= S.theta ⟨0, hdepth⟩ :=
        S.tau_le_theta ⟨0, hdepth⟩
      _ = 1 := S.top_eq
      _ = rho := hrhoOne.symm
  · have hjpred : j.1 - 1 < depth := by
      have hjle : j.1 <= depth := Nat.le_of_lt_succ j.2
      have hjpos : 0 < j.1 := Nat.pos_of_ne_zero hjzero
      omega
    let m : Fin depth := ⟨j.1 - 1, hjpred⟩
    have hsucc : m.succ = j := by
      apply Fin.ext
      change j.1 - 1 + 1 = j.1
      omega
    simp only [nearestInterval, j, dif_neg hjzero]
    change S.tau m <= rho
    rw [FiniteScaleSequence.tau, hsucc]
    exact hjmem

theorem le_theta_nearestInterval (S : FiniteScaleSequence delta depth)
    (hdepth : 0 < depth) (rho : NNReal)
    (hdelta : delta <= rho) (hrho : rho <= 1) :
    rho <= S.theta (nearestInterval S hdepth rho hdelta) := by
  let j := firstBelow S rho hdelta
  by_cases hjzero : j.1 = 0
  · simp only [nearestInterval, j, dif_pos hjzero]
    calc
      rho <= 1 := hrho
      _ = S.radius 0 := S.top_eq.symm
      _ = S.theta ⟨0, hdepth⟩ := by rfl
  · have hjpred : j.1 - 1 < depth := by
      have hjle : j.1 <= depth := Nat.le_of_lt_succ j.2
      have hjpos : 0 < j.1 := Nat.pos_of_ne_zero hjzero
      omega
    let m : Fin depth := ⟨j.1 - 1, hjpred⟩
    let p : Fin (depth + 1) := m.castSucc
    have hpLt : p < j := by
      change m.1 < j.1
      simp only [m]
      exact Nat.sub_one_lt hjzero
    have hpNot : ¬ (S.radius p <= rho) := by
      intro hp
      have hmin : j <= p := firstBelow_le S rho hdelta p hp
      exact (not_le_of_gt hpLt) hmin
    simp only [nearestInterval, j, dif_neg hjzero]
    change rho <= S.theta m
    rw [FiniteScaleSequence.theta]
    exact le_of_not_ge hpNot

end FiniteScaleSequence

/-! ## Actual adjacent covers used for interpolation -/

variable {delta : NNReal} {depth : Nat} {epsilon : Real}
  {iota : Type*} [Fintype iota] [DecidableEq iota]
  {fine : UniformTubeFamily delta iota}
  (C : CoherentStickyMultiscaleCover fine)
  (S : FiniteScaleSequence delta depth)

/-- The actual chosen cover at an intermediate radius in interval `m`. -/
def lowerScaleCover (m : Fin depth) (rho : NNReal)
    (hTauRho : S.tau m <= rho) (hRhoTheta : rho <= S.theta m) :
    StickyScaleCover fine rho :=
  C.base.cover rho ((S.delta_le_tau m).trans hTauRho)
    (hRhoTheta.trans (S.theta_le_one m))

/-- The actual chosen cover at the upper endpoint of interval `m`. -/
def upperEndpointCover (m : Fin depth) :
    StickyScaleCover fine (S.theta m) :=
  C.base.cover (S.theta m)
    ((S.delta_le_tau m).trans (S.tau_le_theta m))
    (S.theta_le_one m)

/-- Literal cross-scale cover from an intermediate radius to its upper
endpoint. -/
def rhoToUpperCover (m : Fin depth) (rho : NNReal)
    (hTauRho : S.tau m <= rho) (hRhoTheta : rho <= S.theta m) :
    StickyScaleCover (lowerScaleCover C S m rho hTauRho hRhoTheta).coarse
      (S.theta m) :=
  C.intervalScaleCover rho (S.theta m)
    ((S.delta_le_tau m).trans hTauRho) hRhoTheta (S.theta_le_one m)

end

end FamilyStickyScaleChainArbitraryRadiusInterpolationV1
