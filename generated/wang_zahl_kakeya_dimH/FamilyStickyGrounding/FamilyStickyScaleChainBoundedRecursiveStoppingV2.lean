import Mathlib

set_option autoImplicit false
set_option warningAsError true

namespace FamilyStickyScaleChainBoundedRecursiveStoppingV2

universe u

/-!
# Generic bounded recursive stopping

This module isolates the finite termination mechanism used by a multiscale
stopping construction.  A successful successor raises a natural-valued stage
by exactly one, while every state has stage at most `N`.  Iterating for the
remaining stage budget therefore computes a terminal state; terminality is a
theorem, not an input field.
-/

/-- A successor system whose successful transitions consume exactly one unit
of a globally bounded natural-valued stage. -/
structure BoundedSuccessorSystem (State : Type u) (N : Nat) where
  stage : State -> Nat
  stage_le : forall s, stage s <= N
  next : State -> Option State
  stage_next : forall {s t}, next s = some t -> stage t = stage s + 1

namespace BoundedSuccessorSystem

variable {State : Type u} {N : Nat}
  (S : BoundedSuccessorSystem State N)

/-- No successor can leave a state already at the global stage bound. -/
theorem next_eq_none_of_stage_eq_bound (s : State)
    (hstage : S.stage s = N) :
    S.next s = none := by
  cases hnext : S.next s with
  | none => rfl
  | some t =>
      have hsuccess := S.stage_next hnext
      have hbound := S.stage_le t
      omega

/-- Every successful transition starts strictly below the global bound. -/
theorem stage_lt_bound_of_next_eq_some {s t : State}
    (hnext : S.next s = some t) :
    S.stage s < N := by
  have hsuccess := S.stage_next hnext
  have hbound := S.stage_le t
  omega

/-- Iterate the successor for at most `fuel` successful transitions, stopping
early as soon as `next` returns `none`. -/
def advance (S : BoundedSuccessorSystem State N) : Nat -> State -> State
  | 0, s => s
  | fuel + 1, s =>
      match S.next s with
      | none => s
      | some t => advance S fuel t

@[simp] theorem advance_zero (s : State) : S.advance 0 s = s := rfl

@[simp] theorem advance_succ_of_next_eq_none (fuel : Nat) (s : State)
    (hnext : S.next s = none) :
    S.advance (fuel + 1) s = s := by
  simp [advance, hnext]

@[simp] theorem advance_succ_of_next_eq_some (fuel : Nat) {s t : State}
    (hnext : S.next s = some t) :
    S.advance (fuel + 1) s = S.advance fuel t := by
  simp [advance, hnext]

/-- Proof-relevant reachability in exactly a specified number of successful
successor steps. -/
inductive ReachesIn (S : BoundedSuccessorSystem State N) :
    Nat -> State -> State -> Prop
  | zero (s : State) : ReachesIn S 0 s s
  | succ {steps : Nat} {s t u : State}
      (hnext : S.next s = some t)
      (hrest : ReachesIn S steps t u) :
      ReachesIn S (steps + 1) s u

/-- Exact stage accounting along a proof-relevant run. -/
theorem stage_eq_of_reachesIn {steps : Nat} {s t : State}
    (hreach : S.ReachesIn steps s t) :
    S.stage t = S.stage s + steps := by
  induction hreach with
  | zero s => simp
  | succ hnext hrest ih =>
      rw [ih, S.stage_next hnext]
      omega

/-- Any fueled iteration is reachable by no more than the supplied fuel. -/
theorem advance_reachesIn_le (fuel : Nat) (s : State) :
    exists steps, steps <= fuel /\
      S.ReachesIn steps s (S.advance fuel s) := by
  induction fuel generalizing s with
  | zero =>
      exact ⟨0, le_rfl, ReachesIn.zero s⟩
  | succ fuel ih =>
      cases hnext : S.next s with
      | none =>
          exact ⟨0, Nat.zero_le _, by
            simpa [advance, hnext] using ReachesIn.zero (S := S) s⟩
      | some t =>
          rcases ih t with ⟨steps, hsteps, hreach⟩
          exact ⟨steps + 1, by omega, by
            simpa [advance, hnext] using
              ReachesIn.succ (S := S) hnext hreach⟩

/-- The stage never decreases under fueled iteration. -/
theorem stage_le_advance (fuel : Nat) (s : State) :
    S.stage s <= S.stage (S.advance fuel s) := by
  rcases S.advance_reachesIn_le fuel s with ⟨steps, -, hreach⟩
  rw [S.stage_eq_of_reachesIn hreach]
  exact Nat.le_add_right _ _

/-- A predicate preserved by every successful transition is preserved by
every proof-relevant finite run. -/
theorem invariant_of_reachesIn (P : State -> Prop)
    (hstep : forall {s t}, S.next s = some t -> P s -> P t)
    {steps : Nat} {s t : State} (hreach : S.ReachesIn steps s t)
    (hs : P s) : P t := by
  induction hreach with
  | zero s => exact hs
  | succ hnext hrest ih =>
      exact ih (hstep hnext hs)

/-- Consequently, a transition invariant survives every fueled iteration. -/
theorem invariant_advance (P : State -> Prop)
    (hstep : forall {s t}, S.next s = some t -> P s -> P t)
    (fuel : Nat) {s : State} (hs : P s) :
    P (S.advance fuel s) := by
  rcases S.advance_reachesIn_le fuel s with ⟨steps, -, hreach⟩
  exact S.invariant_of_reachesIn P hstep hreach hs

/-- Once the supplied fuel covers the remaining stage budget, the fueled run
must end at a state where `next` returns `none`. -/
theorem next_advance_eq_none_of_remaining_le (fuel : Nat) (s : State)
    (hremaining : N - S.stage s <= fuel) :
    S.next (S.advance fuel s) = none := by
  induction fuel generalizing s with
  | zero =>
      have hstage : S.stage s = N := by
        have hbound := S.stage_le s
        omega
      simpa [advance] using S.next_eq_none_of_stage_eq_bound s hstage
  | succ fuel ih =>
      cases hnext : S.next s with
      | none =>
          simp [advance, hnext]
      | some t =>
          have hsuccess := S.stage_next hnext
          have hbound := S.stage_le t
          have hremaining_t : N - S.stage t <= fuel := by
            omega
          simpa [advance, hnext] using ih t hremaining_t

/-- The canonical terminal state, obtained by running for exactly the
remaining bounded stage budget. -/
def terminalState (s : State) : State :=
  S.advance (N - S.stage s) s

/-- The canonical result is genuinely terminal. -/
theorem next_terminalState_eq_none (s : State) :
    S.next (S.terminalState s) = none := by
  exact S.next_advance_eq_none_of_remaining_le
    (N - S.stage s) s le_rfl

/-- The canonical terminal state is reachable from the initial state. -/
theorem terminalState_reachesIn (s : State) :
    exists steps, steps <= N - S.stage s /\
      S.ReachesIn steps s (S.terminalState s) := by
  exact S.advance_reachesIn_le (N - S.stage s) s

/-- The stage can only increase on the way to the canonical terminal state. -/
theorem stage_le_terminalState (s : State) :
    S.stage s <= S.stage (S.terminalState s) := by
  exact S.stage_le_advance (N - S.stage s) s

/-- Every transition invariant possessed by the initial state is possessed by
the computed terminal state. -/
theorem invariant_terminalState (P : State -> Prop)
    (hstep : forall {s t}, S.next s = some t -> P s -> P t)
    {s : State} (hs : P s) :
    P (S.terminalState s) := by
  exact S.invariant_advance P hstep (N - S.stage s) hs

/-- A terminal input is unchanged by every fueled iteration. -/
theorem advance_eq_self_of_next_eq_none (fuel : Nat) (s : State)
    (hnext : S.next s = none) :
    S.advance fuel s = s := by
  cases fuel with
  | zero => rfl
  | succ fuel => simp [advance, hnext]

/-- In particular, the terminal-state operation fixes terminal inputs. -/
theorem terminalState_eq_self_of_next_eq_none (s : State)
    (hnext : S.next s = none) :
    S.terminalState s = s := by
  exact S.advance_eq_self_of_next_eq_none (N - S.stage s) s hnext

#print axioms BoundedSuccessorSystem.next_eq_none_of_stage_eq_bound
#print axioms BoundedSuccessorSystem.stage_lt_bound_of_next_eq_some
#print axioms BoundedSuccessorSystem.stage_eq_of_reachesIn
#print axioms BoundedSuccessorSystem.advance_reachesIn_le
#print axioms BoundedSuccessorSystem.next_terminalState_eq_none
#print axioms BoundedSuccessorSystem.invariant_terminalState

end BoundedSuccessorSystem

end FamilyStickyScaleChainBoundedRecursiveStoppingV2
