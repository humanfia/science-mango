import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41MarcusTardosActualFirstRegularLeaderV1
import Mathlib.Tactic

set_option autoImplicit false

namespace FamilyStickyCinematicL32Prop41MarcusTardosActualLeaderNodeCodeV1

open FamilyStickyCinematicL32Prop41MarcusTardosCyclicCoreV1
open FamilyStickyCinematicL32Prop41MarcusTardosActualFirstRegularLeaderV1

/-! # A proof-irrelevant coordinate code for dependent leader nodes -/

def leaderNodeCode
    {symbol : Type*} [DecidableEq symbol]
    {depth : Nat} (A B : DistinctCyclicSequence symbol)
    (node : Sigma (LeaderPair (depth := depth) A B)) :
    Nat × (Nat × Nat) :=
  (node.1.1, (node.2.1.1, node.2.2.1))

theorem leaderNodeCode_injective
    {symbol : Type*} [DecidableEq symbol]
    {depth : Nat} (A B : DistinctCyclicSequence symbol) :
    Function.Injective (leaderNodeCode (depth := depth) A B) := by
  rintro ⟨la, ia, ja⟩ ⟨lb, ib, jb⟩ h
  have hl : la = lb := by
    apply Fin.ext
    exact congrArg (fun z => z.1) h
  subst lb
  have hi : ia = ib := by
    apply Fin.ext
    exact congrArg (fun z => z.2.1) h
  have hj : ja = jb := by
    apply Fin.ext
    exact congrArg (fun z => z.2.2) h
  subst ib
  subst jb
  rfl

#print axioms leaderNodeCode
#print axioms leaderNodeCode_injective

end FamilyStickyCinematicL32Prop41MarcusTardosActualLeaderNodeCodeV1
