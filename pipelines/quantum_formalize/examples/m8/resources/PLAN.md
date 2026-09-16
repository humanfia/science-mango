# Revised M8 resource route

Source: `/home/jing/m8-proof-source-20260916`, commit `3e875907b35ed6d3ecdc031789cc78df00c745b8`; `research_checkpoints/m8_acceptance_20260916/PROOF.md`, JSON argument §7, read with §§2–6. `ACCEPTANCE.json` expressly excludes the original all-input gate, M9, practical performance and runtime extraction. Its acceptance flags are provenance, not Lean premises.

Use `n=N+1`, `M8.Cutoff.limit N = min (N-1) (Nat.log 2 (N+1))`, and the **actual discovered** `R=M6.ActualTransfer.span a' b'`. Recognition proves `R≤limit N`; with `N>0` this supplies `R<N`, `2^R≤n`, and `4^R≤n²`. Do not impose a small-span hypothesis on rejected inputs. Failed discovery and NoLogical are charged by their actual executed branches.

## First independent batch: cutoff

`examples/m8/cutoff`, project `/home/jing/m8-lean-cutoff-formalization`, module `M8Cutoff`, namespace `M8.Cutoff`.

Eight closed targets: `limit_bounds`, `bit_length_limit`, `state_bound`, `state_square`, `indexed_work_envelopes`, `indexed_storage_envelope`, `coefficient_capacity`, `anchor_trial_envelope`. The last only proves the arithmetic inequality `2*N*a*b≤2*N³` when `a,b≤N`; root discovery must still prove that its executed cursor has this trial bound. These definitions contain no resource counter equated to a desired polynomial bound.

## Exact accepted reuse

All paths below are under `pipelines/quantum_formalize/examples/m6`; their canonical manifests, original receipts/drafts, rendered-source hashes and portable declarations must be checked before importing into a resource child. Inspection of interfaces here is not a claim that those imports have already been promoted.

| Existing module / archive | Useful public API | M8 use |
|---|---|---|
| `M6TransferCoefficientsAccepted`, `transfer/coefficients/experiment` | `Transfer.layers_mass`, `trace_coefficient_bound`, `actual_trace_intermediates` | One-start mass ≤8^i; complete and partial trace coefficients ≤`2^R*8^N`. |
| `M6TransferPartialResourcesAccepted`, `transfer/partial_resources/experiment` | `scatter_prefix_magnitude`, `actual_layer_intermediates` | Bounds every partial scatter update and event term, including cancellation. |
| `M6WeightResourcesAccepted`, `transfer/weight_resources/experiment` | `ActualTransfer.boundary_indexed_resources`, `character_indexed_resources` | Instantiate resource guarantees with the actual physical pinned boundary and character weights, eliminating arbitrary W/weight-cost assumptions. |
| `M6TransferActualResourcesAccepted`, `transfer/actual_resources/experiment` | `Transfer.actual_signed_capacity`, `actual_trace_work_bound`, `actual_trace_storage_bound` | Existing actual scatter layout, accumulator widths, address and local-weight charges. |
| `M6SolveResourcesAccepted`, `transfer/solve_resources/experiment` | `ActualTransfer.actual_distance_work`, `actual_witness_work` | Actual counters ≤`50000*N³*4^R` and `200000*N⁴*4^R`; the latter uses an actual `solve=some(d,v,k)` result, not a supplied query-budget oracle. |
| `M6SolveStorageAccepted`, `transfer/solve_storage/experiment` | `ActualTransfer.actual_solve_storage` | Actual reusable workspace ≤`16384*N²*2^R`, including concrete Euclid slots. |
| `M6EuclidAccepted`, `euclid/experiment` | `Euclid.preprocess_correct_cost` | Actual two-gcd preprocessing equals full gcd and costs ≤`180*(N+1)³` for degrees ≤N. No radical/squarefree replacement. |
| `M6EuclidStorageAccepted`, `euclid_storage/experiment` | Concrete machine/slot safety closure | Preserve the real preprocessing storage, not infer storage from its time bound. |

`transfer/FINAL_RESOURCE_API.md` documents exact counters, physical weight costs, preprocessing shared across queries, and non-runtime scope. M7's `GeneratedLabels.pointwise`/resource composition is a pattern for extracting the M6 contract, **not** a dependency on an M7 generated family: M8 starts from one explicit input and one actual discovered transform.

The physical agent's `M8.PhysicalBridge.pointwise_optimizer` will provide the complete `M6.Final.PointwiseCorrect` for the actual transformed polynomial pair. Root discovery will establish its equal-positive-weight, connectivity and two-anchor conditions. Resource composition may alternatively use the already accepted actual M6 resource theorems directly after proving `span<N`; neither approach leaves a free optimizer-correctness/cost premise in final M8.

## Proposed exact downstream API and DAG

Names in this section are proposed interfaces, not already proved declarations.

1. **Discovery instrumentation (root's algorithm, separate from cutoff).** Instrument its actual first-success lexicographic loops over `(exchange,t,alpha,beta)`; invalid t is tested and skipped, both labels retained at N=1. Prove projection to the chosen discovery result and visited trials ≤`2*N*A.card*B.card≤2*N³`. Charge actual support scans, unit gcd tests, modular multiply/reduce, two output-array construction and bound tests. A first-success run can only shorten complete rejection. A current trial uses reused arrays; no orbit or trial list is stored. Conservative bit charges for the explicit residue arithmetic have size bounded by `O(log(N+1))`, giving the source `O(N⁴ log² n)⊆O(n⁶)`; an arbitrary trial evaluator is not free.
2. **Actual optimizer cutoff specialization.** Theorems should conclude, for the actual discovered pair, `actualDistanceWork≤50000*n⁵`, `actualWitnessWork≤200000*n⁶`, and `actualSolveStorage≤16384*n³`. Derive actual `solve` query count from its accepted result, not from a caller-supplied bound. Coordinate transport, transition construction and direct verification have separate actual bounded loops before being absorbed. Parent physical correctness already supplies the meaning of the result and minimum witness.
3. **Coefficient and signed-bit closure.** Instantiate actual pinned weights, then transport the accepted `2^R*8^N` bounds to actual trace and partial arrays. `coefficient_capacity` gives a safe strict power-of-two capacity with `4*(N+1)` magnitude bits; use an extra sign bit as required by the existing signed representation. Reuse actual coefficient additions, degree≤2 multiplication, right-shift/exact-division and first-positive scan guarantees. Negative intermediates remain allowed. Do not prove only the final nonnegative Q bound and omit intermediate values.
4. **Whole indexed algorithm.** Define an instrument whose work is the sum of **executed** original-gcd/discovery/transformed-gcd/optimizer/transport/optional-verification charges and whose workspace is a reused peak, not a sum of all pinned-query memories. Prove projection to root's actual three-way result. Discharge `≤C_index*n⁶` and data/working storage `≤C_store*n³` with fixed constants. `NoLogical` and `Unrecognized` branches must be included. Optional final verification need not be added as a new acceptance requirement, but if included its actual binary elimination is charged.
5. **Faithful tagged sequential store: genuine missing M6/M7 bridge.** M6 provides an indexed-array model, not the requested common sequential simulation. Specify finite tagged-bit records, a cursor that scans records, and read/write operations that compare bounded binary address strings and copy/update the corresponding bit. Count executed tag comparisons, scanned bits, writes and scratch copies; prove lookup/update projection to the corresponding indexed memory operation, well-formed tags and reuse of a single bounded store. Address widths come from the actual allocation bound and accepted layout, not an arbitrary address-width premise at final root. With ≤`C_store*n³` payload bits, O(log n)-bit addresses can conservatively be bounded by O(n); tagged store and scratch therefore fit `C_tag*n⁴`. A deliberately loose `C_access*n⁶` charge per indexed bit operation is enough, but it must follow from this actual scan/copy counter. It must **not** be the definition of read/write cost.
6. **Closed sequential composition.** Lift the indexed operation sequence/loop to the verified tagged-store interpreter; compose each read/write/arithmetic instruction simulation and use the actual indexed work count. This gives fixed constants `C_seq*n¹²` time and `C_space*n⁴` storage for every valid input and all three outcomes. A generic simulation lemma may have premises; final M8 must instantiate them with the actual algorithm and proven store/layout bounds. No Python/Lean-runtime or full Turing-machine extraction requirement is added.

Dependency order: cutoff and measured discovery can run independently; physical optimizer correctness and existing M6 signed-resource imports can run independently; cutoff + successful discovery → actual optimizer specialization; discovery + optimizer + transport → full indexed bound; tagged-store primitives can be prepared independently against the concrete bit-store representation; only full indexed projection/bounds + concrete store simulation → the final n¹²/n⁴ theorem.

## Audit boundaries

- The accepted M6 limits already eliminate the exponential state parameter under the fixed cutoff. They do not by themselves establish discovery/rejection costs or a sequential-store simulation.
- A theorem bounding `discoveryTrials=N³`, `sequentialWork=n¹²`, or an arbitrary evaluator's supplied cost would be circular. These are forbidden shortcuts.
- Do not replace the source's authoritative anchors by translation-pair enumeration and assert identical first results. The recognized sets agree; their first lexicographic witnesses may differ.
- The explicit input length is N, not log N. Even orders, repeated polynomial factors, N=1 and R=0 remain present. The original all-input solver and M9 are excluded.
