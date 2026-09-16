import M8SolverAccepted
import M8DiscoveryResourcesAccepted
import M8OptimizerResourcesAccepted
import M8BankLayoutAccepted

namespace M8.WholeResources
/-- Standard binary primitive charges on the explicit N-bit input model.
The counters describe the specified algorithm, not Lean evaluator time. -/
def inputScanWork (N : ℕ) : ℕ :=
  (List.range (2*N)).foldl (fun w _ => w + 4*(N+1)) 0
/-- Fixed input-validation pass over the two blocks: coordinate differences,
standard binary gcd updates and weight/cursor bookkeeping. Public correctness
still has Valid as its domain; no new InvalidInput outcome is introduced. -/
def connectivityScanWork (N : ℕ) : ℕ :=
  (List.range (2*N)).foldl (fun w _ => w + (64*(N+1)^2 + 8*(N+1))) 0
/-- Clear the concrete reusable allocation once; cache cutoff/control words. -/
noncomputable def setupWork (N : ℕ) : ℕ :=
  M8.BankLayout.payloadSlots N + inputScanWork N + connectivityScanWork N + 32*(N+1)^2
/-- Scan two literal blocks: subtract, multiply, reduce and assign each output bit.
The fixed charge also covers the successful unit/inverse parameter conversion. -/
def transformWork (N : ℕ) : ℕ :=
  (List.range (2*N)).foldl (fun w _ => w + 16*(N+1)^2) 0 + 64*(N+1)^2
/-- One standard extended binary gcd/inverse and the actual two-block undo scan. -/
def undoWork (N : ℕ) : ℕ :=
  (List.range (2*N)).foldl (fun w _ => w + 16*(N+1)^2) 0 + 128*(N+1)^2
noncomputable def originalWork {N : ℕ} [NeZero N] (c : M7.Action.Recipe N) : ℕ :=
  M6.Euclid.preprocessBitCost N (M7.Supports.polynomial c.1)
    (M7.Supports.polynomial c.2) (M6.Cyclic.modulus N)
structure Run (N : ℕ) where
  outcome : M8.Solver.Outcome N
  charges : List ℕ
  discoveryCalls : ℕ
  optimizerCalls : ℕ
/-- Each expensive algorithm is called once on its actual branch.
Charges are ghost accounting of the standard indexed-bit model; they do not
execute an additional Euclidean or optimizer computation. The list has at most
six stage totals, not a stored history of individual queries or accesses. -/
noncomputable def run {N : ℕ} [NeZero N] (c : M7.Action.Recipe N) : Run N := by
  classical
  let F := M8.Solver.originalF c
  let initial := [setupWork N, originalWork c]
  exact if F = 1 then ⟨.noLogical F,initial,0,0⟩ else
    let search := M8.DiscoveryResources.run c
    let stageCharges := initial ++ [M8.DiscoveryResources.charged N search]
    match search.selected.map Prod.snd with
    | none => ⟨.unrecognized F,stageCharges,1,0⟩
    | some choice =>
      let transformed := M8.Discovery.transformed c choice
      let a := M7.Supports.polynomial transformed.1
      let b := M7.Supports.polynomial transformed.2
      match M8.PhysicalBridge.solve transformed with
      | none => ⟨.unrecognized F,stageCharges ++ [transformWork N,
          M6.ActualTransfer.actualDistanceWork N a b],1,1⟩
      | some (d,v,k) => ⟨.recognized F d
          (M8.PhysicalBridge.undo (M8.Discovery.action choice) v) choice k,
          stageCharges ++ [transformWork N,M6.ActualTransfer.actualWitnessWork N a b k,undoWork N],1,1⟩
noncomputable def indexedWork {N : ℕ} [NeZero N] (c : M7.Action.Recipe N) : ℕ :=
  (run c).charges.sum
end M8.WholeResources
