import M8RawParametersAccepted
import M8DiscoveryAccepted
import M8OrbitSpanAccepted
namespace M8.Solver
abbrev BP := M6.Cyclic.BinaryPolynomial
inductive Outcome (N : ℕ) where
  | noLogical (F : BP)
  | unrecognized (F : BP)
  | recognized (F : BP) (d : ℕ) (z : M6.Pinned.Vector (2*N)) (choice : M8.Discovery.Choice N) (queries : ℕ)
def outputF {N : ℕ} : Outcome N → BP
  | .noLogical F => F
  | .unrecognized F => F
  | .recognized F _ _ _ _ => F
noncomputable def originalF {N : ℕ} [NeZero N] (c : M7.Action.Recipe N) : BP :=
  (M6.Euclid.preprocess (M7.Supports.polynomial c.1) (M7.Supports.polynomial c.2) (M6.Cyclic.modulus N)).value
noncomputable def run {N : ℕ} [NeZero N] (c : M7.Action.Recipe N) : Outcome N := by
  classical
  let F := originalF c
  exact if F = 1 then .noLogical F else
    match M8.Discovery.discover c with
    | none => .unrecognized F
    | some choice =>
      match M8.PhysicalBridge.solve (M8.Discovery.transformed c choice) with
      | none => .unrecognized F
      | some (d,v,k) => .recognized F d (M8.PhysicalBridge.undo (M8.Discovery.action choice) v) choice k
end M8.Solver
