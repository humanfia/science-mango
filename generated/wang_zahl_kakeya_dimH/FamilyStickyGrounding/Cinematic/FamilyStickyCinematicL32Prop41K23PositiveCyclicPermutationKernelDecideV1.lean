import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41K23BalancedRankReductionCleanV1

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

namespace FamilyStickyCinematicL32Prop41K23PositiveCyclicPermutationKernelDecideV1

open FamilyStickyCinematicL32Prop41MarcusTardosFact1BoolParityV1
open FamilyStickyCinematicL32Prop41K23BalancedRankReductionCleanV1

def edgeOfFin (i : Fin 6) : K23Edge :=
  ![(0, 0), (0, 1), (0, 2), (1, 0), (1, 1), (1, 2)] i

def finOfEdge (e : K23Edge) : Fin 6 :=
  ![![0, 1, 2], ![3, 4, 5]] e.1 e.2

def finEdgeEquiv : Fin 6 ≃ K23Edge where
  toFun := edgeOfFin
  invFun := finOfEdge
  left_inv i := by fin_cases i <;> rfl
  right_inv e := by
    rcases e with ⟨h, j⟩
    fin_cases h <;> fin_cases j <;> rfl

def FinHostCyclicPositive (rank : Fin 6 -> Fin 6) (h : Fin 2) : Prop :=
  let a : Fin 6 := if h = 0 then 0 else 3
  let b : Fin 6 := if h = 0 then 1 else 4
  let c : Fin 6 := if h = 0 then 2 else 5
  (rank a < rank b /\ rank b < rank c) \/
  (rank b < rank c /\ rank c < rank a) \/
  (rank c < rank a /\ rank a < rank b)

instance (rank : Fin 6 -> Fin 6) (h : Fin 2) :
    Decidable (FinHostCyclicPositive rank h) := by
  unfold FinHostCyclicPositive
  infer_instance

def FinAlternatingFour {alpha : Type*} [DecidableEq alpha]
    (rank : Fin 6 -> Fin 6) (label : Fin 6 -> alpha) : Prop :=
  exists i0 i1 i2 i3 : Fin 6,
    rank i0 < rank i1 /\ rank i1 < rank i2 /\ rank i2 < rank i3 /\
    label i0 = label i2 /\ label i1 = label i3 /\ label i0 ≠ label i1

instance {alpha : Type*} [DecidableEq alpha]
    (rank : Fin 6 -> Fin 6) (label : Fin 6 -> alpha) :
    Decidable (FinAlternatingFour rank label) := by
  unfold FinAlternatingFour
  infer_instance

/-- Exhaustive kernel computation over exactly the `6! = 720` linear
orders of the six ports. -/
theorem finite_port_alternation :
    forall E : Equiv.Perm (Fin 6),
      FinHostCyclicPositive E 0 -> FinHostCyclicPositive E 1 ->
      FinAlternatingFour E (fun i => (edgeOfFin i).1) \/
        FinAlternatingFour E (fun i => (edgeOfFin i).2) := by
  decide

def HostCyclicPositive (rank : K23Edge -> Fin 6) (h : Fin 2) : Prop :=
  (rank (h, 0) < rank (h, 1) /\ rank (h, 1) < rank (h, 2)) \/
  (rank (h, 1) < rank (h, 2) /\ rank (h, 2) < rank (h, 0)) \/
  (rank (h, 2) < rank (h, 0) /\ rank (h, 0) < rank (h, 1))

theorem alternating_host_or_neighbor_of_positive_cyclic_order
    (rankEquiv : K23Edge ≃ Fin 6)
    (hcyclic : forall h, HostCyclicPositive rankEquiv h) :
    AlternatingFour rankEquiv (fun e => e.1) \/
      AlternatingFour rankEquiv (fun e => e.2) := by
  let E : Equiv.Perm (Fin 6) := finEdgeEquiv.trans rankEquiv
  have hcyclicE0 : FinHostCyclicPositive E 0 := by
    simpa [FinHostCyclicPositive, HostCyclicPositive, E, finEdgeEquiv,
      edgeOfFin] using hcyclic 0
  have hcyclicE1 : FinHostCyclicPositive E 1 := by
    simpa [FinHostCyclicPositive, HostCyclicPositive, E, finEdgeEquiv,
      edgeOfFin] using hcyclic 1
  rcases finite_port_alternation E hcyclicE0 hcyclicE1 with hhost | hneighbor
  · left
    rcases hhost with ⟨i0, i1, i2, i3, h01, h12, h23, h02, h13, hne⟩
    refine ⟨edgeOfFin i0, edgeOfFin i1, edgeOfFin i2, edgeOfFin i3, ?_⟩
    simpa [E, finEdgeEquiv] using And.intro h01
      (And.intro h12 (And.intro h23 (And.intro h02 (And.intro h13 hne))))
  · right
    rcases hneighbor with ⟨i0, i1, i2, i3, h01, h12, h23, h02, h13, hne⟩
    refine ⟨edgeOfFin i0, edgeOfFin i1, edgeOfFin i2, edgeOfFin i3, ?_⟩
    simpa [E, finEdgeEquiv] using And.intro h01
      (And.intro h12 (And.intro h23 (And.intro h02 (And.intro h13 hne))))

#print axioms finite_port_alternation
#print axioms alternating_host_or_neighbor_of_positive_cyclic_order

end FamilyStickyCinematicL32Prop41K23PositiveCyclicPermutationKernelDecideV1
