import FamilyStickyGrounding.FamilyStickyAtEveryScaleCoreV1

open scoped BigOperators ENNReal NNReal

namespace FamilyStickyDeltaMaxFiniteChainV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

/-!
# Finite-chain submultiplicativity for sticky Kakeya

This module isolates the finite multiplicative argument in Lemma 7.2 of the
streamlined Guth--Wang--Zahl proof.  A one-step geometric estimate is required
at each adjacent pair of scales; the theorem below composes those local
estimates and does not assume the final product bound.

The actual local factor of a `StickyScaleCover` is also exposed as the
supremum of the genuine `maximalConcentration`s of its active fine fibers.
-/

namespace StickyScaleCover

variable {delta rho : NNReal} {iota : Type*}
  [Fintype iota] [DecidableEq iota]
  {fine : UniformTubeFamily delta iota}

/-- The paper's local `Delta_max` factor at one scale: the largest actual
maximal concentration among the active fine fibers. -/
def fiberDeltaMax (S : StickyScaleCover fine rho) : ENNReal :=
  ⨆ k : {k // k ∈ S.activeCoarse},
    maximalConcentration (S.fiberFamily k.1)

/-- The paper's coarse `Delta_max` at one scale. -/
def coarseDeltaMax (S : StickyScaleCover fine rho) : ENNReal :=
  maximalConcentration S.activeCoarseFamily

/-- Each genuine fiber concentration is bounded by the local scale factor. -/
theorem maximalConcentration_fiber_le_fiberDeltaMax
    (S : StickyScaleCover fine rho) (k : {k // k ∈ S.activeCoarse}) :
    maximalConcentration (S.fiberFamily k.1) <= fiberDeltaMax S := by
  exact le_iSup
    (fun q : {q // q ∈ S.activeCoarse} =>
      maximalConcentration (S.fiberFamily q.1)) k

/-- A uniform bound on all active fibers bounds the local `Delta_max`. -/
theorem fiberDeltaMax_le
    (S : StickyScaleCover fine rho) {C : ENNReal}
    (h : forall k, k ∈ S.activeCoarse ->
      maximalConcentration (S.fiberFamily k) <= C) :
    fiberDeltaMax S <= C := by
  apply iSup_le
  intro k
  exact h k.1 k.2

/-- The Katz--Tao at-scale predicate is exactly a bound on the coarse factor. -/
theorem isKatzTaoAtScale_iff_coarseDeltaMax_le
    (S : StickyScaleCover fine rho) (C : ENNReal) :
    S.IsKatzTaoAtScale C <-> coarseDeltaMax S <= C := by
  exact S.isKatzTaoAtScale_iff_maximalConcentration_le C

end StickyScaleCover

/-- A finite sequence of `Delta_max` values with the local one-step
submultiplicative estimates from Lemma 7.2.

`deltaMax m` is the remaining global concentration at level `m`, while
`localDeltaMax m` is the worst rescaled fiber factor for the step from `m` to
`m+1`.  `dimensionalLoss` is the paper's fixed `C(n)` loss. -/
structure FiniteDeltaMaxChain (depth : Nat) where
  deltaMax : Nat -> ENNReal
  localDeltaMax : Nat -> ENNReal
  dimensionalLoss : ENNReal
  step_le : forall m, m < depth ->
    deltaMax m <=
      (dimensionalLoss * localDeltaMax m) * deltaMax (m + 1)
  top_le_one : deltaMax depth <= 1

/-- Pure finite-chain multiplication: adjacent step bounds compose into the
product of all local factors. -/
theorem deltaMax_le_prod_local
    (depth : Nat) (deltaMax localFactor : Nat -> ENNReal)
    (hstep : forall m, m < depth ->
      deltaMax m <= localFactor m * deltaMax (m + 1)) :
    deltaMax 0 <=
      (∏ m ∈ Finset.range depth, localFactor m) * deltaMax depth := by
  induction depth with
  | zero => simp
  | succ n ih =>
      have hprefix : forall m, m < n ->
          deltaMax m <= localFactor m * deltaMax (m + 1) := by
        intro m hm
        exact hstep m (hm.trans (Nat.lt_succ_self n))
      have hprev := ih hprefix
      have hlast := hstep n (Nat.lt_succ_self n)
      calc
        deltaMax 0 <=
            (∏ m ∈ Finset.range n, localFactor m) * deltaMax n := hprev
        _ <= (∏ m ∈ Finset.range n, localFactor m) *
            (localFactor n * deltaMax (n + 1)) := by
          gcongr
        _ = (∏ m ∈ Finset.range (n + 1), localFactor m) *
            deltaMax (n + 1) := by
          rw [Finset.prod_range_succ]
          ac_rfl

/-- Lemma 7.2's displayed normal form: a fixed dimensional loss occurs once
per scale step, and the top-level concentration is normalized by one. -/
theorem deltaMax_le_dimensionalLoss_pow_mul_prod_local
    (depth : Nat) (deltaMax localDeltaMax : Nat -> ENNReal)
    (dimensionalLoss : ENNReal)
    (hstep : forall m, m < depth ->
      deltaMax m <=
        (dimensionalLoss * localDeltaMax m) * deltaMax (m + 1))
    (htop : deltaMax depth <= 1) :
    deltaMax 0 <=
      dimensionalLoss ^ depth *
        (∏ m ∈ Finset.range depth, localDeltaMax m) := by
  have hchain := deltaMax_le_prod_local depth deltaMax
    (fun m => dimensionalLoss * localDeltaMax m) hstep
  calc
    deltaMax 0 <=
        (∏ m ∈ Finset.range depth,
          dimensionalLoss * localDeltaMax m) * deltaMax depth := hchain
    _ <= (∏ m ∈ Finset.range depth,
          dimensionalLoss * localDeltaMax m) * 1 := by
      gcongr
    _ = dimensionalLoss ^ depth *
        (∏ m ∈ Finset.range depth, localDeltaMax m) := by
      rw [mul_one, Finset.prod_mul_distrib]
      simp

namespace FiniteDeltaMaxChain

/-- The packaged finite chain gives the exact source product estimate. -/
theorem global_le
    {depth : Nat} (C : FiniteDeltaMaxChain depth) :
    C.deltaMax 0 <=
      C.dimensionalLoss ^ depth *
        (∏ m ∈ Finset.range depth, C.localDeltaMax m) := by
  exact deltaMax_le_dimensionalLoss_pow_mul_prod_local
    depth C.deltaMax C.localDeltaMax C.dimensionalLoss C.step_le C.top_le_one

end FiniteDeltaMaxChain

#print axioms StickyScaleCover.maximalConcentration_fiber_le_fiberDeltaMax
#print axioms StickyScaleCover.isKatzTaoAtScale_iff_coarseDeltaMax_le
#print axioms deltaMax_le_prod_local
#print axioms FiniteDeltaMaxChain.global_le

end

end FamilyStickyDeltaMaxFiniteChainV2
