import FamilyStickyGrounding.FamilyStickyDeltaMaxFiniteChainV2

set_option autoImplicit false

open Set
open scoped BigOperators ENNReal NNReal

namespace FamilyStickyDividingScalesFiniteStoppingV1

open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDeltaMaxFiniteChainV2
open Submission.Kakeya.Uniformity

noncomputable section

/-!
# Sticky Kakeya: finite dividing-scales stopping skeleton

This module isolates the finite stopping argument behind Section 7's
`dividingScalesLemma`.  A terminal adjacent interval is either large, or it
carries the no-further-split lower bound.  Finiteness alone then gives the
source dichotomy: all intervals are large, or one long interval carries the
lower bound.  The maintained adjacent/global upper bounds are transported to
the same witness.

The module does not assume the final dichotomy, random translations, or any
geometric thickening theorem.  Converting the all-large branch to a literal
at-every-scale statement remains an explicit interpolation input.
-/

/-- A finite decreasing sequence
`1 = radius 0 >= ... >= radius depth = delta`. -/
structure FiniteScaleSequence (delta : NNReal) (depth : Nat) where
  radius : Fin (depth + 1) -> NNReal
  antitone_radius : Antitone radius
  top_eq : radius 0 = 1
  bottom_eq : radius (Fin.last depth) = delta

namespace FiniteScaleSequence

variable {delta : NNReal} {depth : Nat}

/-- Upper endpoint of adjacent interval `m`. -/
def theta (S : FiniteScaleSequence delta depth) (m : Fin depth) : NNReal :=
  S.radius m.castSucc

/-- Lower endpoint of adjacent interval `m`. -/
def tau (S : FiniteScaleSequence delta depth) (m : Fin depth) : NNReal :=
  S.radius m.succ

theorem delta_le_tau (S : FiniteScaleSequence delta depth) (m : Fin depth) :
    delta <= S.tau m := by
  calc
    delta = S.radius (Fin.last depth) := S.bottom_eq.symm
    _ <= S.radius m.succ := S.antitone_radius (Fin.le_last _)
    _ = S.tau m := rfl

theorem tau_le_theta (S : FiniteScaleSequence delta depth) (m : Fin depth) :
    S.tau m <= S.theta m := by
  apply S.antitone_radius
  exact Fin.castSucc_le_succ m

theorem theta_le_one (S : FiniteScaleSequence delta depth) (m : Fin depth) :
    S.theta m <= 1 := by
  rw [← S.top_eq]
  apply S.antitone_radius
  exact Fin.zero_le _

/-- The paper's terminal condition that an adjacent scale ratio is at least
`delta ^ epsilon`. -/
def IsLarge (S : FiniteScaleSequence delta depth) (epsilon : Real)
    (m : Fin depth) : Prop :=
  (delta : ENNReal) ^ epsilon * (S.theta m : ENNReal) <=
    (S.tau m : ENNReal)

/-- Negation of `IsLarge`, weakened from strict to non-strict form.  This is
the scale separation `tau <= delta ^ epsilon * theta` used by conclusion
(ii) of the source lemma. -/
def IsLong (S : FiniteScaleSequence delta depth) (epsilon : Real)
    (m : Fin depth) : Prop :=
  (S.tau m : ENNReal) <=
    (delta : ENNReal) ^ epsilon * (S.theta m : ENNReal)

/-- The buffered middle interval in conclusion (ii). -/
def IsBuffered (S : FiniteScaleSequence delta depth) (epsilon : Real)
    (m : Fin depth) (rho : NNReal) : Prop :=
  (S.tau m : ENNReal) *
        (((S.theta m / S.tau m : NNReal) : ENNReal) ^ epsilon) <= rho ∧
    (rho : ENNReal) <=
      (S.theta m : ENNReal) *
        (((S.tau m / S.theta m : NNReal) : ENNReal) ^ epsilon)

/-- Every terminal interval is large. -/
def AllStepsLarge (S : FiniteScaleSequence delta depth)
    (epsilon : Real) : Prop :=
  forall m, S.IsLarge epsilon m

/-- Pure finite stopping lemma.  If every terminal interval is either large
or has a no-split certificate, then either all are large or a long certified
interval exists. -/
theorem allStepsLarge_or_exists_long
    (S : FiniteScaleSequence delta depth) (epsilon : Real)
    (barrier : Fin depth -> Prop)
    (hterminal : forall m, S.IsLarge epsilon m ∨ barrier m) :
    S.AllStepsLarge epsilon ∨
      exists m, S.IsLong epsilon m ∧ barrier m := by
  classical
  by_cases hall : S.AllStepsLarge epsilon
  · exact Or.inl hall
  · right
    simp only [AllStepsLarge, not_forall] at hall
    obtain ⟨m, hm⟩ := hall
    refine ⟨m, ?_, (hterminal m).resolve_left hm⟩
    exact le_of_not_ge hm

end FiniteScaleSequence

/-- Data maintained by the Frostman version of the finite stopping process.
The two upper bounds are the invariants before the attempted split; the
terminal alternative records failure of every possible buffered split. -/
structure FrostmanStoppingRun
    (delta : NNReal) (depth N : Nat) (epsilon : Real)
    (eta : Nat -> Real) (S : FiniteScaleSequence delta depth) where
  stage : Nat
  stage_pos : 1 <= stage
  stage_le : stage <= N
  eta_monotone : Monotone eta
  eta_stage_le_epsilon : eta stage <= epsilon
  fineFiberValue : Fin depth -> ENNReal
  adjacentValue : Fin depth -> ENNReal
  middleValue : Fin depth -> NNReal -> ENNReal
  fineFiber_upper : forall m,
    fineFiberValue m <=
      (((S.tau m / delta : NNReal) : ENNReal) ^ eta (stage - 1))
  adjacent_upper : forall m,
    adjacentValue m <=
      (((S.theta m / S.tau m : NNReal) : ENNReal) ^ eta (stage - 1))
  terminal : forall m, S.IsLarge epsilon m ∨
    forall rho, S.IsBuffered epsilon m rho ->
      (((rho / S.tau m : NNReal) : ENNReal) ^ eta stage) <=
        middleValue m rho

/-- Exact output carried by a long terminal Frostman interval. -/
structure FrostmanDividingWitness
    (delta : NNReal) (N : Nat) (epsilon : Real) (eta : Nat -> Real) where
  tau : NNReal
  theta : NNReal
  stage : Nat
  stage_pos : 1 <= stage
  stage_le : stage <= N
  delta_le_tau : delta <= tau
  tau_le_theta : tau <= theta
  theta_le_one : theta <= 1
  long : (tau : ENNReal) <= (delta : ENNReal) ^ epsilon * (theta : ENNReal)
  fineFiberValue : ENNReal
  adjacentValue : ENNReal
  middleValue : NNReal -> ENNReal
  fineFiber_upper : fineFiberValue <=
    (((tau / delta : NNReal) : ENNReal) ^ eta (stage - 1))
  adjacent_upper : adjacentValue <=
    (((theta / tau : NNReal) : ENNReal) ^ eta (stage - 1))
  middle_lower : forall rho : NNReal,
    (tau : ENNReal) *
          (((theta / tau : NNReal) : ENNReal) ^ epsilon) <= rho ->
      (rho : ENNReal) <=
          (theta : ENNReal) *
            (((tau / theta : NNReal) : ENNReal) ^ epsilon) ->
      (((rho / tau : NNReal) : ENNReal) ^ eta stage) <= middleValue rho

namespace FrostmanStoppingRun

variable {delta : NNReal} {depth N : Nat} {epsilon : Real}
  {eta : Nat -> Real} {S : FiniteScaleSequence delta depth}

/-- The finite Frostman stopping process yields either the all-large branch
or the full adjacent/global exponent witness at one long interval. -/
theorem allLarge_or_witness
    (R : FrostmanStoppingRun delta depth N epsilon eta S) :
    S.AllStepsLarge epsilon ∨
      Nonempty (FrostmanDividingWitness delta N epsilon eta) := by
  let barrier : Fin depth -> Prop := fun m =>
    forall rho, S.IsBuffered epsilon m rho ->
      (((rho / S.tau m : NNReal) : ENNReal) ^ eta R.stage) <=
        R.middleValue m rho
  rcases S.allStepsLarge_or_exists_long epsilon barrier R.terminal with
    hall | ⟨m, hlong, hbarrier⟩
  · exact Or.inl hall
  · right
    exact ⟨{
      tau := S.tau m
      theta := S.theta m
      stage := R.stage
      stage_pos := R.stage_pos
      stage_le := R.stage_le
      delta_le_tau := S.delta_le_tau m
      tau_le_theta := S.tau_le_theta m
      theta_le_one := S.theta_le_one m
      long := hlong
      fineFiberValue := R.fineFiberValue m
      adjacentValue := R.adjacentValue m
      middleValue := R.middleValue m
      fineFiber_upper := R.fineFiber_upper m
      adjacent_upper := R.adjacent_upper m
      middle_lower := by
        intro rho hlower hupper
        exact hbarrier rho ⟨hlower, hupper⟩ }⟩

/-- Thin adapter to the literal at-every-scale API.  The finite stopping
logic supplies the disjunction; only interpolation of an all-large terminal
chain is left as an explicit input. -/
theorem frostmanAtEveryScale_or_witness
    {iota : Type*} [Fintype iota] [DecidableEq iota]
    {fine : UniformTubeFamily delta iota}
    (M : StickyMultiscaleCover fine) (error : ENNReal)
    (R : FrostmanStoppingRun delta depth N epsilon eta S)
    (hall : S.AllStepsLarge epsilon ->
      M.IsFrostmanAtEveryScale error) :
    M.IsFrostmanAtEveryScale error ∨
      Nonempty (FrostmanDividingWitness delta N epsilon eta) := by
  rcases R.allLarge_or_witness with hlarge | hwitness
  · exact Or.inl (hall hlarge)
  · exact Or.inr hwitness

end FrostmanStoppingRun

/-- Data maintained by the Katz--Tao version.  Its top/global upper bound is
oriented as `theta ^ (-eta_(j-1))`; the adjacent and buffered bounds have the
same orientation as Part (B) of the source lemma. -/
structure KatzTaoStoppingRun
    (delta : NNReal) (depth N : Nat) (epsilon : Real)
    (eta : Nat -> Real) (S : FiniteScaleSequence delta depth) where
  stage : Nat
  stage_pos : 1 <= stage
  stage_le : stage <= N
  eta_monotone : Monotone eta
  eta_stage_le_epsilon : eta stage <= epsilon
  globalValue : Fin depth -> ENNReal
  adjacentValue : Fin depth -> ENNReal
  middleValue : Fin depth -> NNReal -> ENNReal
  global_upper : forall m,
    globalValue m <= (S.theta m : ENNReal) ^ (-eta (stage - 1))
  adjacent_upper : forall m,
    adjacentValue m <=
      (((S.theta m / S.tau m : NNReal) : ENNReal) ^ eta (stage - 1))
  terminal : forall m, S.IsLarge epsilon m ∨
    forall rho, S.IsBuffered epsilon m rho ->
      (((S.theta m / rho : NNReal) : ENNReal) ^ eta stage) <=
        middleValue m rho

/-- Exact output carried by a long terminal Katz--Tao interval. -/
structure KatzTaoDividingWitness
    (delta : NNReal) (N : Nat) (epsilon : Real) (eta : Nat -> Real) where
  tau : NNReal
  theta : NNReal
  stage : Nat
  stage_pos : 1 <= stage
  stage_le : stage <= N
  delta_le_tau : delta <= tau
  tau_le_theta : tau <= theta
  theta_le_one : theta <= 1
  long : (tau : ENNReal) <= (delta : ENNReal) ^ epsilon * (theta : ENNReal)
  globalValue : ENNReal
  adjacentValue : ENNReal
  middleValue : NNReal -> ENNReal
  global_upper : globalValue <= (theta : ENNReal) ^ (-eta (stage - 1))
  adjacent_upper : adjacentValue <=
    (((theta / tau : NNReal) : ENNReal) ^ eta (stage - 1))
  middle_lower : forall rho : NNReal,
    (tau : ENNReal) *
          (((theta / tau : NNReal) : ENNReal) ^ epsilon) <= rho ->
      (rho : ENNReal) <=
          (theta : ENNReal) *
            (((tau / theta : NNReal) : ENNReal) ^ epsilon) ->
      (((theta / rho : NNReal) : ENNReal) ^ eta stage) <= middleValue rho

namespace KatzTaoStoppingRun

variable {delta : NNReal} {depth N : Nat} {epsilon : Real}
  {eta : Nat -> Real} {S : FiniteScaleSequence delta depth}

/-- The finite Katz--Tao stopping process yields either the all-large branch
or one long interval with the exact Part (B) exponent orientations. -/
theorem allLarge_or_witness
    (R : KatzTaoStoppingRun delta depth N epsilon eta S) :
    S.AllStepsLarge epsilon ∨
      Nonempty (KatzTaoDividingWitness delta N epsilon eta) := by
  let barrier : Fin depth -> Prop := fun m =>
    forall rho, S.IsBuffered epsilon m rho ->
      (((S.theta m / rho : NNReal) : ENNReal) ^ eta R.stage) <=
        R.middleValue m rho
  rcases S.allStepsLarge_or_exists_long epsilon barrier R.terminal with
    hall | ⟨m, hlong, hbarrier⟩
  · exact Or.inl hall
  · right
    exact ⟨{
      tau := S.tau m
      theta := S.theta m
      stage := R.stage
      stage_pos := R.stage_pos
      stage_le := R.stage_le
      delta_le_tau := S.delta_le_tau m
      tau_le_theta := S.tau_le_theta m
      theta_le_one := S.theta_le_one m
      long := hlong
      globalValue := R.globalValue m
      adjacentValue := R.adjacentValue m
      middleValue := R.middleValue m
      global_upper := R.global_upper m
      adjacent_upper := R.adjacent_upper m
      middle_lower := by
        intro rho hlower hupper
        exact hbarrier rho ⟨hlower, hupper⟩ }⟩

/-- Thin adapter to the literal at-every-scale Katz--Tao API. -/
theorem katzTaoAtEveryScale_or_witness
    {iota : Type*} [Fintype iota] [DecidableEq iota]
    {fine : UniformTubeFamily delta iota}
    (M : StickyMultiscaleCover fine) (error : ENNReal)
    (R : KatzTaoStoppingRun delta depth N epsilon eta S)
    (hall : S.AllStepsLarge epsilon ->
      M.IsKatzTaoAtEveryScale error) :
    M.IsKatzTaoAtEveryScale error ∨
      Nonempty (KatzTaoDividingWitness delta N epsilon eta) := by
  rcases R.allLarge_or_witness with hlarge | hwitness
  · exact Or.inl (hall hlarge)
  · exact Or.inr hwitness

end KatzTaoStoppingRun

/-- Reuse of the frozen finite `Delta_max` chain: a product budget at a
specified exponent automatically gives the source global upper bound. -/
theorem FiniteDeltaMaxChain.global_le_exponent_of_productBudget
    {depth : Nat} (C : FiniteDeltaMaxChain depth)
    (theta : NNReal) (eta : Real)
    (hbudget :
      C.dimensionalLoss ^ depth *
          (∏ m ∈ Finset.range depth, C.localDeltaMax m) <=
        (theta : ENNReal) ^ (-eta)) :
    C.deltaMax 0 <= (theta : ENNReal) ^ (-eta) :=
  C.global_le.trans hbudget

#print axioms FiniteScaleSequence.allStepsLarge_or_exists_long
#print axioms FrostmanStoppingRun.allLarge_or_witness
#print axioms FrostmanStoppingRun.frostmanAtEveryScale_or_witness
#print axioms KatzTaoStoppingRun.allLarge_or_witness
#print axioms KatzTaoStoppingRun.katzTaoAtEveryScale_or_witness
#print axioms FiniteDeltaMaxChain.global_le_exponent_of_productBudget

end

end FamilyStickyDividingScalesFiniteStoppingV1
