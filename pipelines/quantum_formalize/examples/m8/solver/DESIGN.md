# Actual three-branch solver design

The following concrete definitions are prepared for freezing only after all parent canonical gates are verified. The nested optimizer-none fallback returns Unrecognized operationally; optimizer_present proves that branch unreachable for a valid discovered input with nonunit full gcd. Queries are internal metadata. No analysis-only orbit minimum occurs in run.

```lean
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
```

Planned nine-node DAG: originalF_signature; literal_span_le; discovery_span; optimizer_present; output_gcd ← originalF_signature; noLogical_exact ← originalF_signature; unrecognized_exact and recognized_exact ← originalF_signature, discovery_span, optimizer_present; recognized_correct ← originalF_signature plus imported physical minimum and raw dimension contracts. Every initial context is empty and imported proof premises are canonical verified theorems. The exact graph is generated with the actual definitions and compiled before any model launch.

The recognized contract preserves original F, actual chosen discovery record, original physical quantum distance, inverse-coordinate LX witness and weight, global lower bound over original LX, actual query count ≤2N, lexicographically first successful trial, and the actual rank-defined encoded qubit count. The two rejection contracts are exact F=1 and F≠1 with orbitSpan>limit, respectively.
