# M8 continuous research frontier — navigation only

Revised M8 structured acceptance is OPEN. Former all-input target is deferred M9.
Assemble and verify the revised M8 end-to-end theorem; do not require M9 closure.
Review verdicts are provenance, not mathematical premises. Read full cited sources when invoked.
Already covered: tensor-parity cores; N=2m odd-m correction-aware reduction with exponential optimization.
Move beyond these scopes; do not call exponential reduction a polynomial solver.

# M8 — Recognizable structured exact physical-distance algorithms

User-authorized revision 2026-09-16. This task and MILESTONE_ROADMAP_CURRENT_20260916.md supersede old M8 scope instructions, including strategy v2. The old all-input gate is M9. Obligation ID: m8_structured. M8 is OPEN pending acceptance.

## Domain and outputs
Input explicit block length N and two nonempty binary supports of equal positive weight, connected under the original within-block-difference gcd criterion. Retain all even orders and repeated-root multiplicities. C=ker[b a], D=im(a,b), F=gcd(a,b,x^N+1), k=2deg F. Preserve physical coefficient Hamming weight and the original recipe group: independent translations, one common unit multiplier, block exchange.
Compute F exactly. F=1 returns NoLogical. Otherwise a deterministic polynomial-time recognizer must either accept a declared structural regime and output exact physical distance and an attaining nonboundary physical witness, or return Unrecognized. Unrecognized is neither NoLogical nor a hardness conclusion. Do not silently drop even inputs: state precisely which are recognized and leave others Unrecognized.

## Required consolidated deliverable
1. Specify the recognized class mathematically, with a deterministic recognizer and representation discovery. Fix all regime constants independently of N (e.g. a fixed c in width<=c log2(N+1)); total bit-time/storage exponents cannot depend on uncontrolled input parameters. Test a discovered representation; do not assume a supplied optimal order.
2. Assemble sound applicable scalar-core results and physical optimization interfaces. A scalar minimum alone is not a physical-distance solver: prove physical-weight and nonboundary witness transport wherever used. Provide at least one explicit infinite admitted non-Cartesian physical family with successful recognition; do not claim novelty beyond every earlier regime without proof. State coverage and overlap with M6 honestly.
3. Prove exactness, minimum-witness decoding, and worst-case polynomial bit-time and storage for accepted inputs AND recognition/rejection. Include preprocessing, representation discovery, big-integer coefficients, and witness extraction. Exponential-width algorithms qualify only on the explicitly recognized bounded-parameter regime; they need not cover all inputs.
4. Give a complete algorithmic specification and end-to-end theorem with full dependency closure, an acceptance checklist, explicit exclusions and residual M9 obligations. Any executed implementation must include reproducible checks and negative controls; full production software and formal proof-assistant verification are separate milestones.
5. Freeze the consolidated artifact and obtain two independent matching full-scope reviews under THIS revised gate. Local review votes are provenance, not premises. Do not mark M8 complete merely because its scope changed. No claim that original all-input M8/M9 is solved.

## Planner allocation
Lane 1: assemble the recognized-class end-to-end exact physical solver from existing results; fill only actual missing correctness/algorithm interfaces. Lane 2: independently establish coverage, discovery costs, uniform polynomial resources and physical witness transport, including explicit accepted non-Cartesian infinite families and rejected cases. These are synthesis and validation tasks, not duplicate reviews of a single old lemma. Candidate dual reviewers remain separate.
At every batch inspect the last three batches. Prefer completing this acceptance checklist over accumulating further local counterexamples or special-family catalogues. State each remaining acceptance item. General hardness and all-input optimization belong to deferred M9; do not require them to close M8.

## Last three completed batches — mandatory planner checkpoint
[
  {
    "run": "run-7koxumjf",
    "summary_status": "reviewed_candidate_pending_manual_integration",
    "reviewed_claims": [
      {
        "candidate_sha256": "94f42a9b7a9f01e55ed787c461828c567e258dc24276eeda33e03a62cffab008",
        "proof_path": "docs/proof-fd39ff50501693e6b53e63ed7894079b5b460ebe19bca306d225282dc8e3fd91.md",
        "claim": "Consolidated mathematical candidate for revised M8 on the fixed c=1 orbit-logarithmic-span class. For every explicit connected equal-positive-weight binary two-block input, the deterministic algorithm below computes the full-multiplicity gcd F, returns NoLogical exactly when F=1, and otherwise accepts exactly when R_orb<=min(N-1,floor(log2(N+1))). Acceptance returns exact physical quantum distance and an attaining original-coordinate nonboundary witness; other surviving inputs return Unrecognized. Total deterministic sequential bit time is O((N+1)^12) and storage O((N+1)^4), including discovery and rejection. Explicit infinite separated-direction-non-Cartesian coverage includes odd and even orders and repeated common factors. This consolidates the two supplied contributions and resolves their discovery, resource-model and coverage interfaces. It supplies the mathematical deliverable ready for freezing, but does not assert an actual freeze, independent full-scope reviews, implementation execution, milestone acceptance or M9 completion.",
        "remaining_obligations": [
          "Freeze this consolidated candidate and its bounded summary, then obtain two fresh independent matching full-scope reviews under the revised M8 checklist. Neither freezing nor those reviews occurred here; M8 acceptance remains open.",
          "Any subsequent executed implementation must provide reproducible validation and negative controls for discovery, multiplicities, signed normalization, character-pin orientation, witness transport and rejection. Production software and formal proof-assistant verification remain separate.",
          "Deferred M9 retains unrestricted optimization and a complete family-preserving hardness alternative. Neither is established by this candidate, and neither is a prerequisite for accepting the stated revised-M8 regime."
        ],
        "scope": "selected_obligation",
        "reviewed_source_run": "run-7koxumjf"
      },
      {
        "candidate_sha256": "abf6635b7fce6a9cde017c9d1aa1e8ad616e154ea23e99003d856f2f203a58ea",
        "proof_path": "docs/proof-d96748b565c4a01d15e70049f254da4b2dc6d3a73fcbb02ed6719a750e89bea0.md",
        "claim": "Coverage/resource compatibility for consolidating drafts 76fdaa and e381e8 is established for their fixed c=1 orbit-logarithmic-span regime. The translation-based coverage and resource arguments apply to 76fdaa's anchor-based discovery and physical optimizer, with the tuple conversion, decoder interface and coverage distinctions below. Common bounds are O((N+1)^6) indexed-array bit work and O((N+1)^3) storage, or conservatively O((N+1)^12) sequential bit time and O((N+1)^4) storage, including rejection. This meets the assigned bounded compatibility-report criterion; it is neither another full solver nor consolidated M8 acceptance.",
        "remaining_obligations": [
          "Incorporate this compatibility report into one authoritative consolidated M8 theorem, algorithm specification, dependency closure and revised acceptance checklist.",
          "Freeze the consolidated artifact and bounded summary, then obtain two fresh independent matching full-scope reviews of both. Neither freezing nor those reviews occurred here.",
          "Any later executed implementation needs reproducible validation and negative controls. Production software and proof-assistant verification remain separate milestones.",
          "General all-input optimization and family-preserving hardness remain deferred M9 obligations; this report establishes neither."
        ],
        "scope": "sublemma",
        "reviewed_source_run": "run-7koxumjf"
      }
    ],
    "dispatch_records": [
      {
        "dispatched_task_ids": [
          "26addc765610e9c081cbd3d967d3fd99f56c80879a0365e505ba124fea3d812d",
          "bef11375f5928038ffb994b8b4e817c2233b733be4a8845b74809869242cb387"
        ],
        "errors": [],
        "status": "planning_only"
      }
    ]
  },
  {
    "run": "run-_3u8fsby",
    "summary_status": "round_limit_reached",
    "reviewed_claims": [
      {
        "candidate_sha256": "f8c44edae58d1f499201828d9c2e353851f1621e7126694cedf966a2cf34500e",
        "proof_path": "docs/proof-cddccd90f8ca32b3e6454a349e36ec9844f375edcd31cbbe4c8f5b05999c3fda.md",
        "claim": "The frozen inputs establish the byte identity and revised-gate specification of the fd39ff consolidated candidate, but do not establish the identity of its reviewed bounded summary or two independent matching full-scope review bodies. The justified controller disposition is evidence reconciliation pending, not integration-ready and not a finding that reviews never occurred. This new acceptance ledger preserves the existing mathematical candidate and its dependency declarations; it does not replace its proof or certify M8 completion.",
        "remaining_obligations": [
          "Recover and verify the candidate serialization-to-manuscript binding and the exact bounded summary identity.",
          "Establish two independent matching full-scope reviews of that candidate-summary pair under the revised gate, including disposition of objections; unavailable bodies do not establish that reviews never occurred.",
          "Complete the separate coverage/applicability attachment and preserve the consolidated candidate's full dependency closure when assessing mathematical acceptance.",
          "Controller integration and M8 acceptance remain pending these checks. Production implementation and formal verification are separate; unrestricted optimization and family-preserving hardness remain deferred M9."
        ],
        "scope": "sublemma",
        "reviewed_source_run": "run-_3u8fsby"
      },
      {
        "candidate_sha256": "82160509fbae8f9445d0c97960ebf2676c044a84e16ab6476cc2b4bd049e06e8",
        "proof_path": "docs/proof-bd07b15cb47483192b4979d70439b3282065fc2b9fefd40e96618669fd486858.md",
        "claim": "Bounded incorporation check: the frozen consolidated candidate fd39ff faithfully incorporates the mathematical coverage, discovery, resource and physical-witness contract of d96748. No substantive mathematical delta is required for their fixed c=1 orbit-logarithmic-span regime. This attachment supplies an exact section mapping and verifies applicability; it does not replace the solver or constitute a full-scope acceptance review. Fidelity of the earlier consolidated bounded summary is not established because that summary was not located in the frozen inputs.",
        "remaining_obligations": [
          "Supply the earlier consolidated bounded summary with its identity and compare its wording against the checked restrictions. Its fidelity is not established by the frozen proof or checkpoint.",
          "In the synthesis lane, reconcile the frozen candidate and summary with the two independent full-scope review bodies under the revised gate. Retrieve existing evidence before concluding that reviews must be repeated; status labels and this attachment do not establish milestone acceptance.",
          "Obtain the required independent checks of this new attachment and its accompanying summary. This coverage/resources attachment is not a substitute for either consolidated full-scope review.",
          "Any future executed implementation requires reproducible checks and negative controls. Production software and proof-assistant verification remain separate.",
          "Unrestricted optimization and family-preserving hardness remain deferred M9 obligations, outside this claim and unnecessary for accepting the stated revised-M8 regime."
        ],
        "scope": "sublemma",
        "reviewed_source_run": "run-_3u8fsby"
      }
    ],
    "dispatch_records": [
      {
        "dispatched_task_ids": [
          "661a30221a1bfc6d55fb2e5c042bc6f7bf65a35986715712d1beea6477309f19",
          "3652526605c599867f0105ec091997431dc556c91380361a5a99164e5f5e95ec"
        ],
        "errors": [],
        "status": "planning_only"
      }
    ]
  },
  {
    "run": "run-ntx68knq",
    "summary_status": "round_limit_reached",
    "reviewed_claims": [
      {
        "candidate_sha256": "4f147d67a4379785859d923fbf5d3c2ab83f122860b157d7fcdaed687c66dad6",
        "proof_path": "docs/proof-5227bf06a774c7b7fe07bd2779cb7afbd4db248945a2841da8de67ae65f96ff2.md",
        "claim": "A concrete review-ready package is supplied for the unchanged fd39ff consolidated manuscript: its verified byte reference, a newly authored bounded summary S1 in this response, a section-addressed revised acceptance checklist, preserved dependency declarations, and an explicit freeze/review handoff. This completes the assigned synthesis-package task, not mathematical acceptance of M8. No summary digest, canonical candidate binding, performed freeze, or matching independent review is asserted.",
        "remaining_obligations": [
          "Independently compare the actual S1 text supplied here with the unchanged manuscript and its invoked proofs; this synthesis attachment does not replace the separate fidelity-validation lane.",
          "Freeze the definitive manuscript/candidate–S1 package, recording exact serialization conventions and hashes. Verify any proposed association with canonical candidate identifier 94f42a before using it.",
          "Obtain Reviewer A's independent matching full-scope report on the definitive candidate and S1 under the revised M8 gate.",
          "Obtain Reviewer B's separate independent matching full-scope report on the same definitive candidate and S1; resolve all actual objections and version differences before controller acceptance.",
          "Any subsequent executed implementation requires reproducible checks and negative controls. Production software and proof-assistant verification remain separate.",
          "Unrestricted optimization and family-preserving hardness remain deferred M9 work; neither is established here or required to complete this bounded synthesis task."
        ],
        "scope": "sublemma",
        "reviewed_source_run": "run-ntx68knq"
      },
      {
        "candidate_sha256": "df07316174e0686a6915d066f69ca50adff3a9e3632a1d808b97961b1ad012c7",
        "proof_path": "docs/proof-1732202f2966f6d564d815be27ca1bf7d50580418ee518680870129643827803.md",
        "claim": "The newly supplied bounded summary S-v1, identified as this response's summary object, faithfully describes the frozen fd39ff consolidated manuscript within its stated mathematical scope. This completes the assigned clause-addressed fidelity comparison for a new summary version, including recognition, multiplicities, physical optimization, witness transport, resources, coverage and exclusions. No correction to the manuscript's mathematical statements is required by this comparison. Historical summary fidelity, serialization binding, independent full-scope review matching and M8 acceptance are not established.",
        "remaining_obligations": [
          "The synthesis/controller lane must select and serialize the definitive candidate-summary pair, preserving K and its recursive declarations. S-v1 is new response text; no summary digest, canonical serialization binding or freeze was performed here.",
          "Obtain two independent matching full-scope reviews of the definitive pair under the revised M8 gate, resolving objections and verifying identities. Historical review occurrence is not disproved; this attachment establishes neither matching bodies nor acceptance.",
          "Any change to S-v1 requires comparison of the changed clauses. Fidelity of an unavailable historical summary remains outside this result.",
          "Future executed implementations require reproducible checks and negative controls. Production software and formal proof-assistant verification remain separate milestones.",
          "Unrestricted exact optimization and family-preserving hardness remain deferred M9 obligations, neither solved here nor prerequisites for accepting the stated structured M8 regime."
        ],
        "scope": "sublemma",
        "reviewed_source_run": "run-ntx68knq"
      }
    ],
    "dispatch_records": [
      {
        "dispatched_task_ids": [
          "6d852d043784cff1f6db2e09738eca6d88fc78a2fa2ca555d4c3b82d40e7bff2",
          "7ae268d3c9d147fe24f54026cc26df7454852ba183bcfff529d6f1d22a386d90"
        ],
        "errors": [],
        "status": "planning_only"
      }
    ]
  }
]
## Reviewed result history
[
  {
    "candidate_sha256": "2778362831418924e0a0c7cf098770d65968b502d1de0198e77f59b47d40e84e",
    "proof_path": "docs/proof-104aaa3517b4c018d263ee0aec9e284530d6b24a3f6387236728ad9166ef4335.md",
    "claim": "Polynomial, optimum-preserving preprocessing for the specified marked physical pricing queries: constructively eliminate every available one- or two-coordinate affine consequence and optimize every zero-column or equal-column parity fiber, repeating until none remain. The output includes an exact objective offset and an explicit original-coordinate decoder. Preprocessing costs O((N+1)^7) bit time and O((N+1)^4) storage, uniformly in span and support weight. This is a new compression component relative to the cited pricing interface, not a uniform optimizer: the residual problem can remain large. The assigned polynomial optimization success criterion and neither original M8 outcome are established.",
    "remaining_obligations": [
      "Supply an oracle-free polynomial exact optimizer for the residual affine weighted problems arising from both marked branches. No uniform residual-size or width bound is established; the assigned optimization success criterion remains unmet.",
      "Prove any larger-fiber elimination mechanism preserves the full joint constraints and exact physical objective, with polynomial construction, state-table size, arithmetic, storage, and witness decoding.",
      "The separate HARDNESS lane still needs a proved established-hard-source theorem and a polynomial-size reduction preserving exactly two circulants, equal positive weights, connectedness, both nonboundary threshold directions, and exclusion of unintended lighter logicals.",
      "Close M8 only through its original uniform-algorithm or family-preserving-hardness outcome, retaining even orders, full gcd multiplicities, NoLogical, the exact recipe group, and connection to justified tractable regimes.",
      "Obtain matching fresh independent dual reviews of this complete candidate and its summary before integration. No execution, independent reviews, or integration occurred in this call."
    ],
    "scope": "sublemma",
    "reviewed_source_run": "run-p86d9_0g"
  },
  {
    "candidate_sha256": "779d1f1c796299a935a4655c179fe7536e2997f70304a3ca460549df9ed8b363",
    "proof_path": "docs/proof-b52a3a55f1c5a53b7c6bdf6004cf9e4ef3503e36ab431d2aab70c955b4989d66.md",
    "claim": "A polynomial-size connected order-padding component preserves exact nonboundary distance and minimum-witness recovery for every binary two-block input with equal positive support weights, including disconnected inputs and even orders. Explicitly, an input of block length n maps to a connected input of length N<4n²+2n, with unchanged distance, unchanged threshold, and full gcd F_out(x)=F_in(x)^D for an explicitly chosen power of two D. Every target nonboundary witness decodes to a source nonboundary witness of no greater physical weight. This proves a normalization component, not the assigned established-hard-source constraint encoding. That assignment and M8 remain unresolved.",
    "remaining_obligations": [
      "Supply a precisely proved established-hard-source theorem; no hardness of the component's intermediate two-block source interface is assumed.",
      "Construct the missing polynomial-size source-constraint encoding into equal-positive-weight two-circulant cycles modulo boundaries, with both threshold directions and decoding of every unintended cyclic combination.",
      "Compose that encoding with the normalization component and verify any additional promises. This component changes logical dimension by D and does not preserve fixed k or fixed support weight.",
      "For the ALGORITHM lane, construct an oracle-free polynomial optimizer for the marked physical pricing queries, including representation discovery, storage, exact arithmetic, and minimum-witness recovery.",
      "Resolve an original M8 outcome and connect any completed hardness result to justified tractable regimes. The present normalization theorem establishes neither outcome.",
      "Obtain matching fresh independent dual reviews of the complete candidate and summary before integration."
    ],
    "scope": "sublemma",
    "reviewed_source_run": "run-p86d9_0g"
  },
  {
    "candidate_sha256": "d58e848950abacc5c3bec2e24cca44e08d32f945e7e724634aded0e48824b26a",
    "proof_path": "docs/proof-dd49488694fbbc18e0cfa0f8df22968253fa0beb71438f2df8128cc67727be4c.md",
    "claim": "Certified weighted column retraction gives a new oracle-free joint-elimination operation for the residual marked physical pricing problems. It preserves every joint syndrome-and-detector minimum-cost fiber, allows overlapping replacement supports of unrestricted size, and retains original-coordinate witness decoding. Deterministic certificate discovery and composition with the supplied preprocessing cost O((N+1)^8) bit time and O((N+1)^4) bits of storage. This establishes the bounded optimization-operation alternative, not a uniform residual optimizer or new family-wide tractable regime. M8 remains open.",
    "remaining_obligations": [
      "Construct a polynomial exact optimizer for terminal residual systems not resolved by the certified retractions and affine preprocessing. No uniform residual-size, width, or certificate-coverage bound is proved.",
      "Establish additional physical-family coverage if claimed; the strict-extension control is an affine optimization example, not a proved cyclic CSS realization.",
      "Develop the separate HARDNESS source encoding, including a proved hard-source theorem, polynomial explicit length, both nonboundary threshold directions, and exclusion of unintended lighter logicals.",
      "Resolve an original M8 outcome while retaining full multiplicities, even orders, NoLogical, physical witnesses, the exact recipe group, and connection to scoped tractable regimes.",
      "Obtain matching fresh independent dual reviews of this complete candidate and its summary before integration. No implementation, execution, reviews, or integration occurred here."
    ],
    "scope": "sublemma",
    "reviewed_source_run": "run-urx2_h0z"
  },
  {
    "candidate_sha256": "47f8f9f230c726c918f352b098dcb5818dfa9474d40da8b146351379066926be",
    "proof_path": "docs/proof-473c098a15888c5cc66982dc9124f70dc506e7ad2f1d6e5c39d6af5a156fafc5.md",
    "claim": "A Boolean circuit with G≥1 gates can be transformed into an explicit binary convolution of length N≤(3G+1)(4G+1), with a prescribed input-support mask, a consecutive output-equation mask, and one marked coordinate. Circuit satisfiability is equivalent to the existence of a marked solution of physical coefficient weight at most G+1. Every such solution decodes to a satisfying assignment; every nontrivial solution on an unsatisfiable instance has weight at least G+3. The construction also defines an auxiliary linear pair whose nontrivial coset is exactly the marked solutions. This supplies a proved hard source and a polynomial convolution encoding, but the masks and auxiliary trivial subspace are additional restrictions, not CSS boundaries. The assigned family-preserving gadget criterion is NOT met; M8 remains open.",
    "remaining_obligations": [
      "Construct a polynomial-size physical gadget enforcing the input-support mask, selected convolution equations and marked nontrivial coset inside exactly two binary circulants.",
      "Prove both target threshold directions for every physical nonboundary, including arbitrary cyclic superpositions; identify the actual boundary image and exclude all unintended lighter logicals.",
      "Produce equal positive support weights and polynomial intermediate length before applying connected normalization. Verify full gcd multiplicities, even orders and NoLogical in the resulting physical construction.",
      "The ALGORITHM lane still requires an oracle-free optimizer for both marked physical pricing queries, with polynomial representation discovery, total bit time, storage and attaining physical witness recovery.",
      "Connect any completed family-preserving hardness theorem to the proved M6 tractable regime. The masked source theorem alone establishes neither original M8 outcome.",
      "Obtain matching fresh independent dual reviews of this unchanged candidate and summary before integration."
    ],
    "scope": "sublemma",
    "reviewed_source_run": "run-urx2_h0z"
  },
  {
    "candidate_sha256": "1842018df25628d5ff1b7df9942384e4bbc326ec6abcfdb2e0d333d5344ed601",
    "proof_path": "docs/proof-76fdaa93638fffb21d39b6594c25101d4a2cdb17a639ba4f800fdf1835df45a7.md",
    "claim": "A deterministic, orbit-logarithmic-span recognizer and exact physical-distance solver is specified and proved below. On every admitted input it computes the full-multiplicity F and returns NoLogical exactly when F=1. Otherwise it accepts exactly when some independently translated, commonly unit-multiplied presentation has anchored span R<=min(N-1,floor(log2(N+1))); on acceptance it returns exact quantum distance and an attaining original-coordinate nonboundary witness, and otherwise returns Unrecognized. The complete pipeline has fixed polynomial bit-time and storage bounds, including rejection. Explicit infinite non-Cartesian coverage is established. This is a new synthesis of discovery, M6 optimization and inverse physical transport, not a new proof of M6 or completion of M8. The separate companion synthesis/verification and two matching independent full-scope reviews are not supplied.",
    "remaining_obligations": [
      "Integrate the separately requested coverage/resource verification with this synthesis, resolving any differences in the intended non-Cartesian coverage criterion or resource model.",
      "Freeze the consolidated candidate and summary and obtain two fresh independent matching full-scope reviews under the revised M8 gate. No such reviews or artifact freeze occurred in this call.",
      "Keep production implementation and formal verification separate; any later executed implementation needs reproducible checks and negative controls.",
      "Deferred M9 retains unrestricted exact optimization and family-preserving hardness. Neither is established or required to prove this baseline."
    ],
    "scope": "sublemma",
    "reviewed_source_run": "run-zxj4st_t"
  },
  {
    "candidate_sha256": "c5447b0877bdea6e6fd6caea4ccb9250e86068cb77e5c203d6ca8720d1e79e9d",
    "proof_path": "docs/proof-e381e8926e19477c14bc07ca8110a0cbe782d5082c9380fde5e83b4ed939cf43.md",
    "claim": "Supporting coverage-and-resources theorem for the fixed c=1 orbit logarithmic-span regime: deterministic representation discovery, exact physical distance and minimum-witness recovery have O((N+1)^6) indexed-array bit work and O((N+1)^3) bits of storage, including unsuccessful recognition. A conservative sequential-access implementation has O((N+1)^10) bit time and O((N+1)^4) storage. The regime includes explicit infinite connected, equal-weight, non-Cartesian physical families at odd and even orders, including inputs with repeated common factors. This meets the assigned supporting-theorem criterion for this baseline, not consolidated M8 acceptance or its required independent reviews.",
    "remaining_obligations": [
      "Integrate this supporting theorem with the synthesis artifact, ensuring that its exact recognized predicate, deterministic discovery, pin orientation, inverse transport and resource model match.",
      "Freeze the consolidated full-scope M8 candidate and obtain two fresh independent matching reviews of both its complete argument and bounded summary. This contribution supplies neither review.",
      "If additional structural or scalar-core branches are included, check their complete proofs and charge their discovery, physical optimization, arithmetic, storage and witness transport separately.",
      "Any future executed implementation requires reproducible validation and negative controls. Production software and formal proof-assistant verification remain separate milestones.",
      "Unrestricted optimization and family-preserving hardness for the unrecognized complement remain deferred M9 work; neither is established or required to prove this supporting theorem."
    ],
    "scope": "sublemma",
    "reviewed_source_run": "run-zxj4st_t"
  },
  {
    "candidate_sha256": "94f42a9b7a9f01e55ed787c461828c567e258dc24276eeda33e03a62cffab008",
    "proof_path": "docs/proof-fd39ff50501693e6b53e63ed7894079b5b460ebe19bca306d225282dc8e3fd91.md",
    "claim": "Consolidated mathematical candidate for revised M8 on the fixed c=1 orbit-logarithmic-span class. For every explicit connected equal-positive-weight binary two-block input, the deterministic algorithm below computes the full-multiplicity gcd F, returns NoLogical exactly when F=1, and otherwise accepts exactly when R_orb<=min(N-1,floor(log2(N+1))). Acceptance returns exact physical quantum distance and an attaining original-coordinate nonboundary witness; other surviving inputs return Unrecognized. Total deterministic sequential bit time is O((N+1)^12) and storage O((N+1)^4), including discovery and rejection. Explicit infinite separated-direction-non-Cartesian coverage includes odd and even orders and repeated common factors. This consolidates the two supplied contributions and resolves their discovery, resource-model and coverage interfaces. It supplies the mathematical deliverable ready for freezing, but does not assert an actual freeze, independent full-scope reviews, implementation execution, milestone acceptance or M9 completion.",
    "remaining_obligations": [
      "Freeze this consolidated candidate and its bounded summary, then obtain two fresh independent matching full-scope reviews under the revised M8 checklist. Neither freezing nor those reviews occurred here; M8 acceptance remains open.",
      "Any subsequent executed implementation must provide reproducible validation and negative controls for discovery, multiplicities, signed normalization, character-pin orientation, witness transport and rejection. Production software and formal proof-assistant verification remain separate.",
      "Deferred M9 retains unrestricted optimization and a complete family-preserving hardness alternative. Neither is established by this candidate, and neither is a prerequisite for accepting the stated revised-M8 regime."
    ],
    "scope": "selected_obligation",
    "reviewed_source_run": "run-7koxumjf"
  },
  {
    "candidate_sha256": "abf6635b7fce6a9cde017c9d1aa1e8ad616e154ea23e99003d856f2f203a58ea",
    "proof_path": "docs/proof-d96748b565c4a01d15e70049f254da4b2dc6d3a73fcbb02ed6719a750e89bea0.md",
    "claim": "Coverage/resource compatibility for consolidating drafts 76fdaa and e381e8 is established for their fixed c=1 orbit-logarithmic-span regime. The translation-based coverage and resource arguments apply to 76fdaa's anchor-based discovery and physical optimizer, with the tuple conversion, decoder interface and coverage distinctions below. Common bounds are O((N+1)^6) indexed-array bit work and O((N+1)^3) storage, or conservatively O((N+1)^12) sequential bit time and O((N+1)^4) storage, including rejection. This meets the assigned bounded compatibility-report criterion; it is neither another full solver nor consolidated M8 acceptance.",
    "remaining_obligations": [
      "Incorporate this compatibility report into one authoritative consolidated M8 theorem, algorithm specification, dependency closure and revised acceptance checklist.",
      "Freeze the consolidated artifact and bounded summary, then obtain two fresh independent matching full-scope reviews of both. Neither freezing nor those reviews occurred here.",
      "Any later executed implementation needs reproducible validation and negative controls. Production software and proof-assistant verification remain separate milestones.",
      "General all-input optimization and family-preserving hardness remain deferred M9 obligations; this report establishes neither."
    ],
    "scope": "sublemma",
    "reviewed_source_run": "run-7koxumjf"
  },
  {
    "candidate_sha256": "f8c44edae58d1f499201828d9c2e353851f1621e7126694cedf966a2cf34500e",
    "proof_path": "docs/proof-cddccd90f8ca32b3e6454a349e36ec9844f375edcd31cbbe4c8f5b05999c3fda.md",
    "claim": "The frozen inputs establish the byte identity and revised-gate specification of the fd39ff consolidated candidate, but do not establish the identity of its reviewed bounded summary or two independent matching full-scope review bodies. The justified controller disposition is evidence reconciliation pending, not integration-ready and not a finding that reviews never occurred. This new acceptance ledger preserves the existing mathematical candidate and its dependency declarations; it does not replace its proof or certify M8 completion.",
    "remaining_obligations": [
      "Recover and verify the candidate serialization-to-manuscript binding and the exact bounded summary identity.",
      "Establish two independent matching full-scope reviews of that candidate-summary pair under the revised gate, including disposition of objections; unavailable bodies do not establish that reviews never occurred.",
      "Complete the separate coverage/applicability attachment and preserve the consolidated candidate's full dependency closure when assessing mathematical acceptance.",
      "Controller integration and M8 acceptance remain pending these checks. Production implementation and formal verification are separate; unrestricted optimization and family-preserving hardness remain deferred M9."
    ],
    "scope": "sublemma",
    "reviewed_source_run": "run-_3u8fsby"
  },
  {
    "candidate_sha256": "82160509fbae8f9445d0c97960ebf2676c044a84e16ab6476cc2b4bd049e06e8",
    "proof_path": "docs/proof-bd07b15cb47483192b4979d70439b3282065fc2b9fefd40e96618669fd486858.md",
    "claim": "Bounded incorporation check: the frozen consolidated candidate fd39ff faithfully incorporates the mathematical coverage, discovery, resource and physical-witness contract of d96748. No substantive mathematical delta is required for their fixed c=1 orbit-logarithmic-span regime. This attachment supplies an exact section mapping and verifies applicability; it does not replace the solver or constitute a full-scope acceptance review. Fidelity of the earlier consolidated bounded summary is not established because that summary was not located in the frozen inputs.",
    "remaining_obligations": [
      "Supply the earlier consolidated bounded summary with its identity and compare its wording against the checked restrictions. Its fidelity is not established by the frozen proof or checkpoint.",
      "In the synthesis lane, reconcile the frozen candidate and summary with the two independent full-scope review bodies under the revised gate. Retrieve existing evidence before concluding that reviews must be repeated; status labels and this attachment do not establish milestone acceptance.",
      "Obtain the required independent checks of this new attachment and its accompanying summary. This coverage/resources attachment is not a substitute for either consolidated full-scope review.",
      "Any future executed implementation requires reproducible checks and negative controls. Production software and proof-assistant verification remain separate.",
      "Unrestricted optimization and family-preserving hardness remain deferred M9 obligations, outside this claim and unnecessary for accepting the stated revised-M8 regime."
    ],
    "scope": "sublemma",
    "reviewed_source_run": "run-_3u8fsby"
  },
  {
    "candidate_sha256": "4f147d67a4379785859d923fbf5d3c2ab83f122860b157d7fcdaed687c66dad6",
    "proof_path": "docs/proof-5227bf06a774c7b7fe07bd2779cb7afbd4db248945a2841da8de67ae65f96ff2.md",
    "claim": "A concrete review-ready package is supplied for the unchanged fd39ff consolidated manuscript: its verified byte reference, a newly authored bounded summary S1 in this response, a section-addressed revised acceptance checklist, preserved dependency declarations, and an explicit freeze/review handoff. This completes the assigned synthesis-package task, not mathematical acceptance of M8. No summary digest, canonical candidate binding, performed freeze, or matching independent review is asserted.",
    "remaining_obligations": [
      "Independently compare the actual S1 text supplied here with the unchanged manuscript and its invoked proofs; this synthesis attachment does not replace the separate fidelity-validation lane.",
      "Freeze the definitive manuscript/candidate–S1 package, recording exact serialization conventions and hashes. Verify any proposed association with canonical candidate identifier 94f42a before using it.",
      "Obtain Reviewer A's independent matching full-scope report on the definitive candidate and S1 under the revised M8 gate.",
      "Obtain Reviewer B's separate independent matching full-scope report on the same definitive candidate and S1; resolve all actual objections and version differences before controller acceptance.",
      "Any subsequent executed implementation requires reproducible checks and negative controls. Production software and proof-assistant verification remain separate.",
      "Unrestricted optimization and family-preserving hardness remain deferred M9 work; neither is established here or required to complete this bounded synthesis task."
    ],
    "scope": "sublemma",
    "reviewed_source_run": "run-ntx68knq"
  },
  {
    "candidate_sha256": "df07316174e0686a6915d066f69ca50adff3a9e3632a1d808b97961b1ad012c7",
    "proof_path": "docs/proof-1732202f2966f6d564d815be27ca1bf7d50580418ee518680870129643827803.md",
    "claim": "The newly supplied bounded summary S-v1, identified as this response's summary object, faithfully describes the frozen fd39ff consolidated manuscript within its stated mathematical scope. This completes the assigned clause-addressed fidelity comparison for a new summary version, including recognition, multiplicities, physical optimization, witness transport, resources, coverage and exclusions. No correction to the manuscript's mathematical statements is required by this comparison. Historical summary fidelity, serialization binding, independent full-scope review matching and M8 acceptance are not established.",
    "remaining_obligations": [
      "The synthesis/controller lane must select and serialize the definitive candidate-summary pair, preserving K and its recursive declarations. S-v1 is new response text; no summary digest, canonical serialization binding or freeze was performed here.",
      "Obtain two independent matching full-scope reviews of the definitive pair under the revised M8 gate, resolving objections and verifying identities. Historical review occurrence is not disproved; this attachment establishes neither matching bodies nor acceptance.",
      "Any change to S-v1 requires comparison of the changed clauses. Fidelity of an unavailable historical summary remains outside this result.",
      "Future executed implementations require reproducible checks and negative controls. Production software and formal proof-assistant verification remain separate milestones.",
      "Unrestricted exact optimization and family-preserving hardness remain deferred M9 obligations, neither solved here nor prerequisites for accepting the stated structured M8 regime."
    ],
    "scope": "sublemma",
    "reviewed_source_run": "run-ntx68knq"
  }
]

## Previous batch failures — do not repeat unchanged

[]
