import FamilyStickyGrounding.FamilyStickyDividingScalesFiniteStoppingV1

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false

open Set
open scoped ENNReal NNReal

namespace FamilyStickyScaleChainTwoExponentStoppingCoreV2

open FamilyStickyDividingScalesFiniteStoppingV1

noncomputable section

/-!
# Two-exponent finite stopping core

The V1 finite stopping API uses one exponent both for the geometric scale gap
and for the target exponent room.  Those roles are independent in the source
argument.  This module records the minimal corrected Katz--Tao core:

* `gapEpsilon` occurs only in `IsLarge`, `IsLong`, and `IsBuffered`;
* `targetExponent` occurs only in the room `eta stage <= targetExponent`.

No interpolation or final sticky-Kakeya theorem is claimed here.  On the
diagonal `gapEpsilon = targetExponent`, the data reduce losslessly to the V1
stopping run.  Off the diagonal, the finite stopping dichotomy remains valid
without imposing any comparison between the two exponents.
-/

/-- The analytic target-exponent room, deliberately independent of every
geometric gap exponent. -/
structure TargetExponentRoom
    (eta : Nat -> Real) (stage : Nat) (targetExponent : Real) : Prop where
  eta_stage_le_target : eta stage <= targetExponent

/-- A small parameter package making the independence of the two exponents
visible at the type level. -/
structure TwoExponentParameters (eta : Nat -> Real) (stage : Nat) where
  gapEpsilon : Real
  targetExponent : Real
  targetRoom : TargetExponentRoom eta stage targetExponent

namespace TwoExponentParameters

variable {eta : Nat -> Real} {stage : Nat}

/-- Target room survives replacement by an arbitrary geometric gap exponent.
This is the formal separation that is absent from the one-parameter API. -/
def replaceGap (P : TwoExponentParameters eta stage) (newGap : Real) :
    TwoExponentParameters eta stage where
  gapEpsilon := newGap
  targetExponent := P.targetExponent
  targetRoom := P.targetRoom

@[simp] theorem replaceGap_gapEpsilon
    (P : TwoExponentParameters eta stage) (newGap : Real) :
    (P.replaceGap newGap).gapEpsilon = newGap := rfl

@[simp] theorem replaceGap_targetExponent
    (P : TwoExponentParameters eta stage) (newGap : Real) :
    (P.replaceGap newGap).targetExponent = P.targetExponent := rfl

@[simp] theorem replaceGap_eta_stage_le_target
    (P : TwoExponentParameters eta stage) (newGap : Real) :
    (P.replaceGap newGap).targetRoom.eta_stage_le_target =
      P.targetRoom.eta_stage_le_target := rfl

/-- In particular, target room can coexist with a gap strictly below one;
it cannot force the V1-degenerate condition `1 <= gapEpsilon`. -/
theorem exists_gap_lt_one_with_same_targetRoom
    (P : TwoExponentParameters eta stage) :
    exists Q : TwoExponentParameters eta stage,
      0 < Q.gapEpsilon ∧ Q.gapEpsilon < 1 ∧
      Q.targetExponent = P.targetExponent := by
  exact ⟨P.replaceGap ((1 : Real) / 2), by norm_num, by norm_num, rfl⟩

end TwoExponentParameters

variable {delta : NNReal} {depth N : Nat}
  {gapEpsilon targetExponent : Real} {eta : Nat -> Real}
  {S : FiniteScaleSequence delta depth}

/-- Corrected finite Katz--Tao stopping run.  The gap exponent controls only
the terminal scale predicates, while the target exponent controls only the
profile room. -/
structure TwoExponentKatzTaoStoppingRun
    (delta : NNReal) (depth N : Nat)
    (gapEpsilon targetExponent : Real)
    (eta : Nat -> Real) (S : FiniteScaleSequence delta depth) where
  stage : Nat
  stage_pos : 1 <= stage
  stage_le : stage <= N
  eta_monotone : Monotone eta
  targetRoom : TargetExponentRoom eta stage targetExponent
  globalValue : Fin depth -> ENNReal
  adjacentValue : Fin depth -> ENNReal
  middleValue : Fin depth -> NNReal -> ENNReal
  global_upper : forall m,
    globalValue m <= (S.theta m : ENNReal) ^ (-eta (stage - 1))
  adjacent_upper : forall m,
    adjacentValue m <=
      (((S.theta m / S.tau m : NNReal) : ENNReal) ^ eta (stage - 1))
  terminal : forall m, S.IsLarge gapEpsilon m ∨
    forall rho, S.IsBuffered gapEpsilon m rho ->
      (((S.theta m / rho : NNReal) : ENNReal) ^ eta stage) <=
        middleValue m rho

/-- Corrected witness at a long terminal interval.  It extends the stable V1
geometric witness at `gapEpsilon`, preventing field drift, and carries only
the additional independent target room. -/
structure TwoExponentKatzTaoDividingWitness
    (delta : NNReal) (N : Nat)
    (gapEpsilon targetExponent : Real) (eta : Nat -> Real)
    extends
      FamilyStickyDividingScalesFiniteStoppingV1.KatzTaoDividingWitness
        delta N gapEpsilon eta where
  targetRoom : TargetExponentRoom eta stage targetExponent


/-- Gap-local terminal data before a target exponent is chosen.  This is the
minimal off-diagonal localization producer interface: all scale predicates
are already localized at `gapEpsilon`, while no target-room comparison is
stored in the data. -/
structure KatzTaoLocalizedNoSplitData
    (delta : NNReal) (depth N : Nat) (gapEpsilon : Real)
    (eta : Nat -> Real) (S : FiniteScaleSequence delta depth) where
  stage : Nat
  stage_pos : 1 <= stage
  stage_le : stage <= N
  eta_monotone : Monotone eta
  globalValue : Fin depth -> ENNReal
  adjacentValue : Fin depth -> ENNReal
  middleValue : Fin depth -> NNReal -> ENNReal
  global_upper : forall m,
    globalValue m <= (S.theta m : ENNReal) ^ (-eta (stage - 1))
  adjacent_upper : forall m,
    adjacentValue m <=
      (((S.theta m / S.tau m : NNReal) : ENNReal) ^ eta (stage - 1))
  terminal_noSplit : forall m, ¬ S.IsLarge gapEpsilon m ->
    ¬ exists rho, S.IsBuffered gapEpsilon m rho ∧
      middleValue m rho <
        (((S.theta m / rho : NNReal) : ENNReal) ^ eta stage)

namespace KatzTaoLocalizedNoSplitData

/-- Attach an independently supplied target room to gap-local no-split data.
Unlike the V1 producer, this requires no comparison `eta stage <= gapEpsilon`.
-/
def toStoppingRun
    (D : KatzTaoLocalizedNoSplitData delta depth N gapEpsilon eta S)
    (room : TargetExponentRoom eta D.stage targetExponent) :
    TwoExponentKatzTaoStoppingRun delta depth N gapEpsilon targetExponent eta S where
  stage := D.stage
  stage_pos := D.stage_pos
  stage_le := D.stage_le
  eta_monotone := D.eta_monotone
  targetRoom := room
  globalValue := D.globalValue
  adjacentValue := D.adjacentValue
  middleValue := D.middleValue
  global_upper := D.global_upper
  adjacent_upper := D.adjacent_upper
  terminal := by
    intro m
    by_cases hlarge : S.IsLarge gapEpsilon m
    · exact Or.inl hlarge
    · right
      intro rho hbuffered
      exact le_of_not_gt fun hstrict =>
        D.terminal_noSplit m hlarge ⟨rho, hbuffered, hstrict⟩


end KatzTaoLocalizedNoSplitData

namespace TwoExponentKatzTaoStoppingRun

/-- The same finite stopping proof as V1, now with independent geometric and
target exponents. -/
theorem allLarge_or_witness
    (R : TwoExponentKatzTaoStoppingRun delta depth N gapEpsilon targetExponent eta S) :
    S.AllStepsLarge gapEpsilon ∨
      Nonempty
        (TwoExponentKatzTaoDividingWitness delta N gapEpsilon targetExponent eta) := by
  let barrier : Fin depth -> Prop := fun m =>
    forall rho, S.IsBuffered gapEpsilon m rho ->
      (((S.theta m / rho : NNReal) : ENNReal) ^ eta R.stage) <=
        R.middleValue m rho
  rcases S.allStepsLarge_or_exists_long gapEpsilon barrier R.terminal with
    hall | ⟨m, hlong, hbarrier⟩
  · exact Or.inl hall
  · right
    exact ⟨{
      tau := S.tau m
      theta := S.theta m
      stage := R.stage
      stage_pos := R.stage_pos
      stage_le := R.stage_le
      targetRoom := R.targetRoom
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

/-- Embed a V1 run on the diagonal where the geometric gap and target
exponents are the same. -/
def ofV1
    {epsilon : Real}
    (R :
      FamilyStickyDividingScalesFiniteStoppingV1.KatzTaoStoppingRun
        delta depth N epsilon eta S) :
    TwoExponentKatzTaoStoppingRun delta depth N epsilon epsilon eta S where
  stage := R.stage
  stage_pos := R.stage_pos
  stage_le := R.stage_le
  eta_monotone := R.eta_monotone
  targetRoom := ⟨R.eta_stage_le_epsilon⟩
  globalValue := R.globalValue
  adjacentValue := R.adjacentValue
  middleValue := R.middleValue
  global_upper := R.global_upper
  adjacent_upper := R.adjacent_upper
  terminal := R.terminal

/-- Forget the V2 separation on the diagonal, recovering exactly the V1 run.
There is intentionally no off-diagonal version: V1 has only one exponent. -/
def toV1
    {epsilon : Real}
    (R : TwoExponentKatzTaoStoppingRun delta depth N epsilon epsilon eta S) :
    FamilyStickyDividingScalesFiniteStoppingV1.KatzTaoStoppingRun
      delta depth N epsilon eta S where
  stage := R.stage
  stage_pos := R.stage_pos
  stage_le := R.stage_le
  eta_monotone := R.eta_monotone
  eta_stage_le_epsilon := R.targetRoom.eta_stage_le_target
  globalValue := R.globalValue
  adjacentValue := R.adjacentValue
  middleValue := R.middleValue
  global_upper := R.global_upper
  adjacent_upper := R.adjacent_upper
  terminal := R.terminal

@[simp] theorem toV1_ofV1
    {epsilon : Real}
    (R :
      FamilyStickyDividingScalesFiniteStoppingV1.KatzTaoStoppingRun
        delta depth N epsilon eta S) :
    (ofV1 R).toV1 = R := by
  cases R
  rfl

/-- Rebuilding a diagonal V2 run after forgetting it to V1 is lossless. -/
@[simp] theorem ofV1_toV1
    {epsilon : Real}
    (R : TwoExponentKatzTaoStoppingRun
      delta depth N epsilon epsilon eta S) :
    ofV1 R.toV1 = R := by
  cases R
  rfl

end TwoExponentKatzTaoStoppingRun
namespace KatzTaoLocalizedNoSplitData

/-- The off-diagonal localized producer feeds the corrected finite dichotomy
directly. -/
theorem allLarge_or_witness
    (D : KatzTaoLocalizedNoSplitData delta depth N gapEpsilon eta S)
    (room : TargetExponentRoom eta D.stage targetExponent) :
    S.AllStepsLarge gapEpsilon ∨
      Nonempty
        (TwoExponentKatzTaoDividingWitness delta N gapEpsilon targetExponent eta) :=
  TwoExponentKatzTaoStoppingRun.allLarge_or_witness (D.toStoppingRun room)

end KatzTaoLocalizedNoSplitData


namespace TwoExponentKatzTaoDividingWitness

/-- Forget only the independent target-room certificate.  The geometric
witness is a V1 witness at the gap exponent. -/
def toV1
    (W :
      TwoExponentKatzTaoDividingWitness delta N gapEpsilon targetExponent eta) :
    FamilyStickyDividingScalesFiniteStoppingV1.KatzTaoDividingWitness
      delta N gapEpsilon eta := W.toKatzTaoDividingWitness

end TwoExponentKatzTaoDividingWitness

namespace TwoExponentKatzTaoStoppingRun

/-- On the diagonal, the V2 dichotomy forgets to the original V1 witness
dichotomy. -/
theorem allLarge_or_v1Witness
    {epsilon : Real}
    (R : TwoExponentKatzTaoStoppingRun delta depth N epsilon epsilon eta S) :
    S.AllStepsLarge epsilon ∨
      Nonempty
        (FamilyStickyDividingScalesFiniteStoppingV1.KatzTaoDividingWitness
          delta N epsilon eta) := by
  rcases R.allLarge_or_witness with hall | hW
  · exact Or.inl hall
  · rcases hW with ⟨W⟩
    exact Or.inr ⟨TwoExponentKatzTaoDividingWitness.toV1 W⟩

end TwoExponentKatzTaoStoppingRun

namespace FiniteScaleSequence

/-- The old one-parameter degeneration is now localized to the geometric gap:
if `gapEpsilon >= 1`, every interval is automatically large.  No target
exponent occurs in this statement. -/
theorem allStepsLarge_of_one_le_gapEpsilon
    (T : FiniteScaleSequence delta depth) {gapEpsilon : Real}
    (hone : (1 : Real) <= gapEpsilon) :
    T.AllStepsLarge gapEpsilon := by
  intro m
  unfold FamilyStickyDividingScalesFiniteStoppingV1.FiniteScaleSequence.IsLarge
  have hdeltaOne : (delta : ENNReal) <= 1 := by
    exact_mod_cast (T.delta_le_tau m).trans
      ((T.tau_le_theta m).trans (T.theta_le_one m))
  have hpower : (delta : ENNReal) ^ gapEpsilon <= (delta : ENNReal) := by
    calc
      (delta : ENNReal) ^ gapEpsilon <=
          (delta : ENNReal) ^ (1 : Real) :=
        ENNReal.rpow_le_rpow_of_exponent_ge hdeltaOne hone
      _ = (delta : ENNReal) := ENNReal.rpow_one delta
  calc
    (delta : ENNReal) ^ gapEpsilon * (T.theta m : ENNReal) <=
        (delta : ENNReal) * 1 := by
      gcongr
      exact_mod_cast T.theta_le_one m
    _ = (delta : ENNReal) := mul_one (delta : ENNReal)
    _ <= (T.tau m : ENNReal) := by
      exact_mod_cast T.delta_le_tau m

/-- Hence a genuinely non-large branch forces only `gapEpsilon < 1`.  It says
nothing about the independent `targetExponent`. -/
theorem gapEpsilon_lt_one_of_not_allStepsLarge
    (T : FiniteScaleSequence delta depth) {gapEpsilon : Real}
    (hnot : ¬ T.AllStepsLarge gapEpsilon) :
    gapEpsilon < 1 := by
  exact lt_of_not_ge fun hone =>
    hnot (allStepsLarge_of_one_le_gapEpsilon T hone)

end FiniteScaleSequence

#print axioms TwoExponentParameters.exists_gap_lt_one_with_same_targetRoom
#print axioms KatzTaoLocalizedNoSplitData.toStoppingRun
#print axioms KatzTaoLocalizedNoSplitData.allLarge_or_witness
#print axioms TwoExponentKatzTaoStoppingRun.allLarge_or_witness
#print axioms TwoExponentKatzTaoStoppingRun.toV1_ofV1
#print axioms TwoExponentKatzTaoStoppingRun.ofV1_toV1
#print axioms TwoExponentKatzTaoStoppingRun.allLarge_or_v1Witness
#print axioms FiniteScaleSequence.allStepsLarge_of_one_le_gapEpsilon
#print axioms FiniteScaleSequence.gapEpsilon_lt_one_of_not_allStepsLarge

end

end FamilyStickyScaleChainTwoExponentStoppingCoreV2
