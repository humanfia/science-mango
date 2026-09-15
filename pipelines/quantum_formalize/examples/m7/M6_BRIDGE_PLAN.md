# M7 physical / M6 bridge: exact planning scope

Planning only. No M7 statement below has been compiled or accepted. No M6 source or frozen target is changed. This plan follows original PROOF §§2–3, 7 and the per-class resource reuse in §11; it does not add M8, implementation, runtime/codegen or a new distance algorithm.

## Local source and accepted interfaces

The original source was read in full: `/home/jing/quantum_code_discovery_proof/research_checkpoints/m7_compact_selector_final_20260915/PROOF.md`. Its file SHA256 is `8ad32a3432f4b7fd3ad15aa4467e0f01255ce593ac9e474b1af38c9424addf19` (the candidate hash printed inside that document is a different artifact).

The M6 final seal result records `original_m6`, `recipe_correct`, `storage_correct` accepted, with assembly, unchanged environment and experiment success. Its legacy component `m5_formalized=false` is not a M7 or M6 failure. Before copying any proof closure into a live M7 project, verify its canonical manifest and transitive payloads; this planning read is not such a promotion receipt.

- `../m6/final/lean/M6FinalDomain.lean` — SHA256 `c4e1499765eeeb6c1d443d9c055d29dea93fdee37a6b7b8c821d2eac1f25f73f`.
- `../m6/final/lean/M6FinalClaims.lean` — SHA256 `167479c4cacbb1eba234dacccd375a90c448b8548591528d414811d52dd221a4`.
- `../m6/final/lean/M6ActualTransfer.lean` — SHA256 `52c061393ea7aa909e720fda781d7a816bc1bb845587ffea39624e376bb36654`.
- `../m6/final/lean/M6Coordinates.lean` — SHA256 `f27b29167da6e0388e87f5a07260b092165ccf5440e601858369fd239429527d`.
- `../m6/final/lean/M6RecipeIsometries.lean` — SHA256 `94d8fa1396c5884a4eccdefa81f83e523028af90b1d6e6e69d599bf1eb1ef784`.
- `../m6/recipe_isometries/experiment/AcceptedExperiment.lean` — SHA256 `637a4702b7e603949168f54df55d23c92996d412d406139e0c0a609562312d0f`.
- `../m6/final/seal/experiment/AcceptedExperiment.lean` — SHA256 `eae7997134c071de4f1329341dfde9e845146f241a8010c65c370b4c1654e3c4`.
- `../m6/final/seal/experiment/result.json` — SHA256 `f0ced2436327c242f81456b7388238ab8487637dbba49d0ea5d646a3b4a6505d`.

Reusable exact APIs:

- `M6.Final.Admissible N a b` is `0<N ∧ a.coeff 0=1 ∧ b.coeff 0=1 ∧ a.support.card=b.support.card ∧ span a b<N ∧ Nat.gcd N ((a.support ∪ b.support).gcd id)=1`. It is explicitly an **anchored** domain.
- `M6.Final.PointwiseCorrect` packages actual `CountingCorrect`, `ParametersCorrect`, `AnswerCorrect`, `ExecutionCorrect`, `StorageCorrect`. It supplies actual Q, no-logical iff signature degree zero, actual solve witness and J witness, exact physical CSS distance, work and storage. Reuse this rather than supply a distance oracle or reprove transfer.
- `M6.Cyclic.signature a b M = EuclideanDomain.gcd (EuclideanDomain.gcd a b) M`; `modulus N = X^N+1`. M7 must bridge its full literal polynomial signature to this exact convention.
- `M6.Coordinates.blockPolynomial N h = Σ i:Fin N, C(h i)*X^i`, `coefficients N a i=a.coeff i.val`, and `encode` uses `AdjoinRoot.mk (modulus N)`. These fix orientation and quotient convention.
- Accepted `M6.RecipeIsometries.translation_isometry`, `multiplier_isometry`, `exchange_isometry` already give bijective actual flattened maps, boundary and cycle membership iff, and weight equality. `shift r a i=a(i-r)` and `multiply u a i=a(u⁻¹*i)`. Translation syndrome is shifted by `r+s`; no shear is involved.
- `M6.Flatten.J` is the swap-and-reverse involution; M6 AnswerCorrect already returns its Z witness. M7 still needs action composition and J-conjugated transport for arbitrary placements.
- M5 stage41 has accepted `shift_card_anchor`, `difference_translation`, `anchored_difference_gcd`; it can shorten the anchored connectivity bridge. Its `differenceGcd` is arithmetic. If M7 defines connectivity as subgroup generation, the equivalence to this arithmetic predicate is a real explicit bridge, not definitional magic.

## Fixed proposed definitions (freeze only after type preflight)

Use `Support N := Finset (ZMod N)` with `[NeZero N]`, `Recipe N := Support N × Support N`. Set `indicator A i := if i∈A then 1 else 0`, `poly A := Σ i∈A, X^i.val`, `sig(A,B) := M6.Cyclic.signature (poly A) (poly B) (M6.Cyclic.modulus N)`. No lists with repeated support positions: these are literal sets; N=1 and full supports remain valid.

Use literal action records `(u : (ZMod N)ˣ, ε : Bool, s t : ZMod N)`, retaining both ε records even at N=1. Select `(Aε,Bε)` by ε, then `act g(A,B)=(image (u*·+s) Aε, image (u*·+t) Bε)`. The M7 group owner supplies this single shared definition; do not create an incompatible local action.

Define `Xmap g := translate N s t ∘ multiplier N u ∘ (if ε then blockExchange N else id)` in exactly that order. Define `Zmap g := J ∘ Xmap g ∘ J`. Thus a returned X witness v maps to Xmap g v; its paired Z witness J v maps to J(Xmap g v). Using Xmap unchanged for both CSS types would be wrong for independent translations.

Define substitution on polynomial coefficients as the finite polynomial `subst u p := Σ i∈p.support, C(p.coeff i)*X^((u*(i:ZMod N)).val)`. Define `tau u F := gcd (modulus N) (subst u F)`, normalized by the existing polynomial gcd. Prove quotient-ring substitution is a ring automorphism with inverse u⁻¹. This finite sum handles F=M (degree N) as well as degree<N; do not silently truncate F before reduction.

## Executable DAG proposal

All nodes have empty harness context, concrete imported definitions, universally quantified exact statements, concurrency16/rounds5/gpt-6-astra medium and Mathlib+Physlib retrieval. Each row can be a small frozen graph; conjunctions can split into independent targets without changing the mathematics. `A,B` below are arbitrary finite supports unless hypotheses are written. Definition modules must first build; then generate exact frozen target files from graph, run runtime `load_graph`, and only then launch proofs. Names are proposed M7 names, not existing Lean receipts.

| ID / proposed targets | Exact mathematical output | Dependencies |
|---|---|---|
| B01 `support_polynomial` | `coefficients N (poly A)=indicator A`; `(poly A).support=A.image ZMod.val`; support card equals A.card; `natDegree(poly A)<N` for N>0; `(poly A).coeff 0=1 ↔ 0∈A`. Includes empty A. | Definition build; M6 coordinates |
| B02 `connected_anchor` | For nonempty A,B and chosen q∈A,r∈B, shifts by −q,−r preserve cards, contain0, and preserve within-block generated subgroup; anchored connectivity iff `Nat.gcd N (((poly A).support ∪ (poly B).support).gcd id)=1`. | B01; optional verified M5 stage41; subgroup/gcd bridge |
| B03 `recipe_admissible` | `0<w`, A.card=w, B.card=w, connected A B, 0∈A,0∈B imply `Admissible N (poly A) (poly B)`; for raw supports exhibit the chosen anchored pair satisfying this. No extra assumption w≥2. | B01 B02 |
| B04 `action_coefficients` | Indicator of act g agrees with the M6 shift/multiply/exchange recipe blocks; `Xmap` is the literal composed M6 flattened coordinate map. | B01; shared M7 action definition |
| B05 `action_logicals` | Xmap bijective; maps boundary/cycle sets iff and preserves weight. Zmap likewise for Z sets; Xmap maps set difference bijectively and `Zmap g (J v)=J(Xmap g v)`. | B04; accepted M6 three isometries, J laws |
| B06 `exact_recipe_labels` | For anchored connected equal-weight recipe, instantiate PointwiseCorrect: actual solve none iff degree sig=0; otherwise returns physical minimum d and witnesses. For any act g recipe, transport those witnesses; physical quantumDistance is identical (including none). | B03 B05; verified M6 final root |
| S01 `quotient_substitution` | Ring equivalence σu on CycleRing N, `σu(mk p)=mk(subst u p)`, inverse σu⁻¹, composition σv∘σu=σ(v*u). Valid even N and N=1. | Shared action/unit conventions; M6 quotient definitions |
| S02 `signature_ideal` | The ideal generated by mk a,mk b equals the principal ideal generated by mk(signature a b M). For monic D,E dividing M, equality of their quotient principal ideals implies D=E. | Polynomial Bezout; exact gcd convention |
| S03 `full_signature_transport` | `sig(act g(A,B))=tau u (sig(A,B))`, including independent translation/exchange invariance; for every monic F∣M, tau u F is monic, divides M, `tau v(tau u F)=tau(v*u)F`, tau1F=F. | B01 B04 S01 S02 |
| S04 `signature_degree_sector` | For monic F∣M, `(tau u F).natDegree=F.natDegree`; hence dimension label invariant and `∃g,sig(act g c)∈E ↔ ∃u,tau u(sig c)∈E`, with literal realizing action `(u,false,0,0)`. | S03; either quotient-ideal rank transport or M6 boundary cardinality plus B05 |
| B07 `presentation_answer_bridge` | For each stored anchored c and action g, returned actual solve witnesses transport to the literal ordered supports act g c, with identical d/k labels and signature tau u(sig c). No additional solver invocation on unanchored outputs. | B06 S04 |

Parallel waves: B01, S01 and S02 can start together; B02/B04 follow B01; B03 and B05 then run independently of S03; B06 and S03 can overlap; S04 and B07 finish the bridge. Sixteen-way concurrency is a cap, not an excuse to remove true dependencies. Group normal-form/counting/canonicalization nodes belong to the other M7 modules, not this bridge.

## Real gaps and boundaries

The main proof work is full signature transport in the nonreduced quotient and its connection to literal gcd, plus the finite support/anchored input and action-wrapper interfaces. Three elementary coordinate isometries, all transfer normalization, actual exact distance, pin recovery and original indexed-array resource bounds already exist; re-proving them would duplicate accepted M6.

S02–S04 must preserve polynomial multiplicities. Equality of root sets, squarefree replacement or assuming odd N would weaken original M7. Conversely, do not add a separate irreducible-factor permutation classification if exact polynomial equality already proves the required transport.

For a generated canonical representative zero belongs to both supports. Raw ordered output presentations usually do not satisfy M6.Admissible; use transport rather than impose a false anchoring requirement on the full orbit. Connectivity of unanchored supports uses differences, not raw exponent gcd. At w=1 connectedness forces N=1; M6 zero-span and no-logical behavior cover this without excluding it. Sector witnesses and winning placements can differ under class-sector semantics; B07 preserves both records instead of conflating their signatures.

M7 §11 sums M6 actual per-class work and reuses the workspace: sum `N^3*4^span(c)` for labels and `N^4*4^span(c)` for witnesses; maximum per-class workspace with separately charged stored representatives/output. The bridge must not claim action placement span is invariant (it is not), or charge new transfer runs for every action when witnesses are transported. No all-span polynomial bound is claimed.

Final integration requires actual verified imports and precise end-to-end theorem fields, not generic free isometry/label-oracle assumptions. This document records a plan and local interface evidence only; neither the planned B/S nodes nor full M7 are marked accepted.
