import M6Euclid

namespace M6.EuclidStorage
open M6.Euclid

/-- Four reusable polynomial registers. saved retains M during the first gcd. -/
structure Slots where
  p : BP
  q : BP
  work : BP
  saved : BP

structure MachineResult where
  slots : Slots
  cancellations : ℕ
  rounds : ℕ
  passes : ℕ

def toRun (r : MachineResult) : Run :=
  ⟨r.slots.p, r.cancellations, r.rounds, r.passes⟩

def offset (r : Run) (c e t : ℕ) : Run :=
  ⟨r.value, c + r.cancellations, e + r.rounds, t + r.passes⟩

/-- Tail-recursive inner loop overwrites only the working remainder slot. -/
noncomputable def remLoop : ℕ → Slots → ℕ → ℕ → MachineResult
  | 0, s, c, t => ⟨s, c, 0, t + 1⟩
  | fuel + 1, s, c, t =>
    if s.q = 0 ∨ s.work = 0 ∨ s.work.degree < s.q.degree then ⟨s, c, 0, t + 1⟩
    else remLoop fuel {s with work := cancel s.work s.q} (c + 1) (t + 2)

/-- After the inner loop, the outer loop reuses its four registers and tail-calls. -/
noncomputable def gcdLoop : ℕ → Slots → ℕ → ℕ → ℕ → MachineResult
  | 0, s, c, e, t => ⟨s, c, e, t + 1⟩
  | fuel + 1, s, c, e, t =>
    if s.q = 0 then ⟨s, c, e, t + 1⟩
    else
      let r := remLoop (rank s.p) ⟨0, s.q, s.p, s.saved⟩ 0 1
      gcdLoop fuel ⟨r.slots.q, r.slots.work, 0, r.slots.saved⟩
        (c + r.cancellations) (e + 1) (t + r.passes + 1)

noncomputable def gcdStart (p q saved : BP) (c e t : ℕ) : MachineResult :=
  gcdLoop (rank q + 1) ⟨p, q, 0, saved⟩ c e (t + 1)

/-- The same registers hold the first result and then the second gcd with M. -/
noncomputable def preprocess (a b M : BP) : MachineResult :=
  let g := gcdStart a b M 0 0 0
  gcdStart g.slots.p g.slots.saved 0 g.cancellations g.rounds g.passes

noncomputable def slotsFit (width : ℕ) (s : Slots) : Prop :=
  rank s.p ≤ width ∧ rank s.q ≤ width ∧ rank s.work ≤ width ∧ rank s.saved ≤ width

/-- All executed inner-loop configurations and final counters fit their registers. -/
noncomputable def remSafe : ℕ → Slots → ℕ → ℕ → ℕ → Prop
  | 0, s, c, t, width => slotsFit width s ∧ c ≤ 32*width ∧ t+1 ≤ 32*width
  | fuel + 1, s, c, t, width =>
    slotsFit width s ∧ fuel+1 ≤ 32*width ∧ c ≤ 32*width ∧ t ≤ 32*width ∧
      (if s.q = 0 ∨ s.work = 0 ∨ s.work.degree < s.q.degree then t+1 ≤ 32*width
       else remSafe fuel {s with work := cancel s.work s.q} (c+1) (t+2) width)

/-- The inner and outer loops share a fixed layout; no recursive array frame is saved. -/
noncomputable def gcdSafe : ℕ → Slots → ℕ → ℕ → ℕ → ℕ → Prop
  | 0, s, c, e, t, width =>
    slotsFit width s ∧ c ≤ 32*width ∧ e ≤ 32*width ∧ t+1 ≤ 32*width
  | fuel + 1, s, c, e, t, width =>
    slotsFit width s ∧ fuel+1 ≤ 32*width ∧ c ≤ 32*width ∧ e ≤ 32*width ∧ t ≤ 32*width ∧
      (if s.q = 0 then t+1 ≤ 32*width else
       remSafe (rank s.p) ⟨0, s.q, s.p, s.saved⟩ 0 1 width ∧
       let r := remLoop (rank s.p) ⟨0, s.q, s.p, s.saved⟩ 0 1
       gcdSafe fuel ⟨r.slots.q, r.slots.work, 0, r.slots.saved⟩
         (c+r.cancellations) (e+1) (t+r.passes+1) width)

noncomputable def preprocessSafe (width : ℕ) (a b M : BP) : Prop :=
  gcdSafe (rank b+1) ⟨a,b,0,M⟩ 0 0 1 width ∧
  let g := gcdStart a b M 0 0 0
  gcdSafe (rank g.slots.saved+1) ⟨g.slots.p,g.slots.saved,0,0⟩
    g.cancellations g.rounds (g.passes+1) width

/-- Concrete allocation: four binary arrays and sixteen bounded control words. -/
def polynomialSlots : List String := ["p", "q", "work", "savedM"]
def controlSlots : List String :=
  ["outerFuel", "innerFuel", "degreeP", "degreeQ", "index", "shift",
   "outerCancels", "outerRounds", "outerPasses", "innerCancels", "innerPasses",
   "phase", "carry", "addressA", "addressB", "addressOut"]
def registerBits (width : ℕ) : ℕ := width + 5

def actualPreprocessStorage (N : ℕ) : ℕ :=
  polynomialSlots.length * (N+1) + controlSlots.length * registerBits (N+1)

/-- Numeric control values read directly from a machine configuration. -/
noncomputable def controlValues (s : Slots) (fuel c e t : ℕ) : List ℕ :=
  [fuel,c,e,t,rank s.p,rank s.q,rank s.work,rank s.saved,s.work.natDegree-s.q.natDegree]

end M6.EuclidStorage
