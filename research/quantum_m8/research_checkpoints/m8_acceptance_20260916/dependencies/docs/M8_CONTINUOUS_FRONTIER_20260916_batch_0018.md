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
    "run": "run-2un_w3td",
    "summary_status": "round_limit_reached",
    "reviewed_claims": [],
    "dispatch_records": [
      {
        "dispatched_task_ids": [],
        "errors": [
          "unlocked or invented dependency: docs/proof-792004a58845a696239d0bdc32a65048cc31ce8b74c62e970c71994193a67a.md"
        ],
        "status": "invalid_plan"
      }
    ]
  },
  {
    "run": "run-p86d9_0g",
    "summary_status": "round_limit_reached",
    "reviewed_claims": [
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
      }
    ],
    "dispatch_records": [
      {
        "dispatched_task_ids": [
          "4d7b53b6408297786794d81f79ade9f30c0c1d8977178b19011a032c11dcb309",
          "884d3ffe59ceac713cb9ce53065446bed57259fb2f8ddf070199dc3f89b8ead8"
        ],
        "errors": [],
        "status": "planning_only"
      }
    ]
  },
  {
    "run": "run-urx2_h0z",
    "summary_status": "round_limit_reached",
    "reviewed_claims": [
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
      }
    ],
    "dispatch_records": [
      {
        "dispatched_task_ids": [
          "c39e35e6d7fa85677bc92d6dd36277351adec0479b3611e275b843a832b45279",
          "fc14a0d302f7579bea6378a5ef7da1ce2c7564524db5333dd04c2a1b3f5d71fd"
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
    "candidate_sha256": "198da18643183cdc3329fff60294e772e501f185edc14499062d65eb3d0252de",
    "proof_path": "docs/proof-f3a3208e78ef728924144f403d32e1905fb28e8634a4b889e8fdd8c214c43913.md",
    "claim": "New Lane A exact-failure result with a constructive compatibility criterion. For t≥6, let s=2t+1, ℓ=2^s−1 and D=2^(t+1). The cyclic ideal Δ obtained by evaluating degree-at-most-t Boolean polynomials with f(0)=0 on GF(2^s)* has dimension (ℓ−1)/2, minimum D, dual minimum D−1, full-period generating idempotent, and support gcd one. It exceeds the previous dimension/codimension enumeration budget and is rejected by the stated punctured Boolean-evaluation recognizer. Nevertheless, assembling every exact projection of the anchored code onto at most k other coordinates, using one globally shared binary assignment, gives minimum 1 whenever k≤D−3. A separating projection of size D−2 is explicitly constructible. More generally, exactness of this projection assembly is equivalent to a specified dual-span condition. This meets the assigned new-attempt/exact-failure alternative, not the unrestricted scalar optimization target or either original M8 gate. M8 remains open.",
    "remaining_obligations": [
      "Construct a polynomial optimizer and attaining-word extractor for unrestricted surviving odd cyclic ideals. The dual-span criterion restores exact membership, but neither bounded projections nor polynomial membership separation supplies the missing optimization theorem.",
      "Advance correction-aware physical minimization on non-Cartesian inputs, including every repeated-root layer. This assigned Lane A result supplies no Lane B optimizer.",
      "Prove physical-weight and nonboundary transport for any scalar optimization or hardness bridge, excluding unintended smaller logicals. The displayed admitted diagonal realization has quantum distance two.",
      "Meet original M8 through an all-input polynomial-bit-time and storage exact-distance/minimum-physical-witness algorithm, or a complete polynomial-size reduction from an established hard source preserving exactly two binary circulant blocks, equal positive weights, connectedness, both physical nonboundary threshold directions, and connection to proved tractable regimes.",
      "Retain all admitted orders, complete gcd multiplicities, NoLogical at F=1, and the exact recipe group in any eventual composition.",
      "Obtain fresh matching independent dual reviews of this complete candidate and summary before integration. No reviews or integration occurred in this call."
    ],
    "scope": "sublemma",
    "reviewed_source_run": "run-clcmhygo"
  },
  {
    "candidate_sha256": "b671ae3975802129ee7e24fcfc334dbd691730f7d0ea365933cb84cf96bfe112",
    "proof_path": "docs/proof-116e303636005fbb35a3ca07fd7b40c77c871b3c81f42ce6e0219ed1da0fe63c.md",
    "claim": "New Lane B exact failure and constructive repair: minimum-cost column-basis compression of the JOINT physical syndrome and logical-detector constraints need not preserve minimum physical weight. For every odd N≥7, the connected equal-weight-two recipe a=1+x, b=1+x² has quantum distance 3, whereas the precisely specified two-detector basis algorithm below returns weight (N+1)/2. Its approximation ratio (N+1)/6 is unbounded. Two coordinated fundamental-circuit updates repair the failing branch on this family. This meets the assigned new-compression exact-failure alternative, but supplies neither an unrestricted optimizer nor a new tractable regime beyond existing fixed-span results. Original M8 remains open.",
    "remaining_obligations": [
      "Construct a polynomial exact optimizer for joint physical constraints beyond the failed basis restriction, with charged representation discovery, arithmetic, storage and minimum-witness extraction. The unrestricted omitted-coordinate optimization remains exponential.",
      "Resolve unrestricted surviving odd cyclic core minima in Lane A; this assigned Lane B candidate supplies no scalar minimum oracle.",
      "Meet original M8 through either an all-input polynomial exact-distance/minimum-physical-witness algorithm, including even orders, full gcd multiplicities and NoLogical, or a complete established-hard-source family-preserving hardness reduction with both threshold directions and no unintended smaller logicals.",
      "Obtain matching fresh independent dual reviews of this complete candidate and its summary before integration. No reviews or integration occurred in this call."
    ],
    "scope": "sublemma",
    "reviewed_source_run": "run-clcmhygo"
  },
  {
    "candidate_sha256": "998f7fde4681aed5fa6c2075e9bf4e4417416ef6c7d211d1cee37dc4c439da66",
    "proof_path": "docs/proof-f01ebc021389e7deb9817f61b19c6c01e8677e45f3796519b9a7edb0750428ea.md",
    "claim": "New Lane A result: almost-complete projection hulls give an exact rounded optimization reduction, but do not permit unrounded weight-preserving recovery. For a nonempty binary set S⊆{0,1}^m with minimum weight r≥2, the minimum L over the intersection of its exact single-coordinate-deletion projection hulls satisfies r−1<L≤r, hence ceil(L)=r. This yields a conditional minimum-and-witness reduction for pinned binary linear codes. On an explicit infinite surviving odd cyclic family beyond the previous enumeration budget, however, L is strictly below the integer minimum: even every projection retaining all but one free coordinate admits a common fractional certificate. The certificate and an attaining scalar word are polynomially constructible. Efficient optimization over the required projection hulls is not established. This meets the assigned new-mechanism/exact-failure alternative, not the unrestricted optimization target or either original M8 gate.",
    "remaining_obligations": [
      "Construct a polynomially discoverable and optimizable representation for the pinned almost-complete projection hulls, or another exact scalar minimum mechanism. The conditional oracle time T(n) and storage S(n) are not bounded polynomially.",
      "Resolve unrestricted surviving odd cyclic cores. The counterfamily and conditional reduction do not constitute an unrestricted minimum algorithm or a new established-hard-source encoding.",
      "Advance Lane B's joint correction-aware physical minima on non-Cartesian inputs, including all higher repeated-root layers; no Lane B optimizer is supplied here.",
      "Prove physical-weight and nonboundary transport for any scalar algorithm or hardness construction. The displayed diagonal realization has quantum distance two and does not transport the growing scalar minimum.",
      "Close original M8 only with a uniform polynomial-bit-time and storage exact-distance/minimum-physical-witness algorithm for every admitted input, or a complete established-hard-source polynomial-size reduction preserving exactly two binary circulant blocks, connectedness, equal positive weights, both nonboundary threshold directions and exclusion of unintended smaller logicals, connected to proved tractable regimes.",
      "Retain all orders, full gcd multiplicities, NoLogical at F=1 and the exact recipe group in any eventual composition.",
      "Obtain matching fresh independent dual reviews of this complete candidate and summary before integration. No reviews or automatic integration occurred."
    ],
    "scope": "sublemma",
    "reviewed_source_run": "run-gqhsy45v"
  },
  {
    "candidate_sha256": "fe3bfecf10030ac0573064f598a649a9cf750b53d09bf38f6e9a659cced63b6b",
    "proof_path": "docs/proof-3963799f14aa94e642481eb861f65c2acfa5b99478d7e661d0cdf94e6ff06ce6.md",
    "claim": "New Lane B candidate: signed parity aggregation gives a necessary-and-sufficient, polynomially checkable criterion for exact separation of the physical fundamental-circuit objective across any specified partition of omitted coordinates. It yields exact optimization and original-coordinate witness recovery with an exponential factor only in the largest resulting interaction component. A proposed shortcut—combining independently improving circuit moves—fails on the infinite connected equal-weight-four family N=5^r, r≥2, a=1+x+x^3+x^4, b=1+x+x^2+x^4: the specified algorithm returns a nonboundary vector of weight 2N although a nonboundary vector of weight five exists. This meets the assigned exact-failure alternative and supplies a constructive separability test; it establishes neither a new unrestricted polynomial regime nor either original M8 closure outcome.",
    "remaining_obligations": [
      "Obtain polynomial exact optimization of the surviving joint parity interactions, or polynomially discover another representation with uniformly controlled optimization cost; the component-size exponent remains unrestricted.",
      "Resolve Lane A's unrestricted surviving odd cyclic core minima and establish physical-weight and nonboundary transport for any scalar bridge.",
      "Meet original M8 through an all-input polynomial-bit-time and storage exact-distance/minimum-physical-witness algorithm, including even orders, full gcd multiplicities and NoLogical, or a complete established-hard-source polynomial-size family-preserving hardness reduction with both threshold directions and no unintended smaller logicals, connected to proved tractable regimes.",
      "Obtain matching fresh independent dual reviews of this complete candidate and summary before integration. No reviews or automatic integration occurred."
    ],
    "scope": "sublemma",
    "reviewed_source_run": "run-gqhsy45v"
  },
  {
    "candidate_sha256": "10d7aed012625b333173f3a68602efa223873fde53d1ee0877c18fa65e8f3a6e",
    "proof_path": "docs/proof-c698efa1c351af1c4be748074111457ef4400425132bb62d383b77e4219c2d2d.md",
    "claim": "New Lane A exact failure of an explicit implementation bridge: constructing pinned projection hulls by listing vertices, even compressed into field-linear symmetry orbits, requires exponential output on an explicit surviving odd cyclic family. For t≥6, n=2^(2t+1)−1 and δ=(n−1)/2, every consistent assignment of at most floor(δ/4) coordinate pins has single-free-coordinate-deletion hulls with at least 2^(δ−q) vertices and at least 2^(δ/2) field-linear orbit records. Every omitted vertex has an exposing integer objective with coefficients ±1 and an objective gap at least one. A precise lazy-pricing interface and an exact exponential fallback are supplied. This meets the assigned exact-failure alternative for this specified representation bridge, not the unrestricted optimization target. Neither original M8 outcome is established.",
    "remaining_obligations": [
      "Construct polynomial exact optimization and attaining-word recovery for unrestricted surviving odd cyclic cores, including arbitrary consistent pins. The vertex-list failure does not exclude compact implicit or extended formulations.",
      "For a lazy projection-hull implementation, prove polynomial signed pricing, representation discovery, iteration count, exact arithmetic, storage, and witness extraction. These bounds are not supplied by membership tests.",
      "Advance joint correction-aware physical optimization for non-Cartesian inputs and every repeated-root layer; establish physical-weight and nonboundary transport for any scalar bridge.",
      "Meet original M8 through a uniform polynomial-bit-time and storage exact-distance/minimum-physical-witness algorithm on every admitted input, or a complete established-hard-source polynomial-size reduction preserving two binary circulant blocks, equal positive weights, connectedness, both nonboundary threshold directions, and exclusion of unintended smaller logicals, connected to proved tractable regimes.",
      "Retain all admitted orders, full gcd multiplicities, NoLogical at F=1, and the exact recipe group in any eventual composition.",
      "Obtain matching fresh independent dual reviews of this complete candidate and summary before integration. No reviews or integration are claimed."
    ],
    "scope": "sublemma",
    "reviewed_source_run": "run-humo1h0e"
  },
  {
    "candidate_sha256": "645bd6c3e41030ac60de901d3013158a8be9a6091e4292cbe873f958d0750d6c",
    "proof_path": "docs/proof-a8052849a54263c1fb945550b9c5589ea296f937f4df26df49cd97e80d8bac7b.md",
    "claim": "New Lane B exact-failure candidate: an exact auxiliary minimum-cut representation of the physical detector-branch objective need not exist, even after arbitrary coordinate complements. For every N=4k+1 with k≥2, the admitted recipe a=1+x, b=1+x² has a specified detector branch whose fundamental-circuit interaction component contains all N omitted coordinates. Its objective is not submodular after any coordinate complements, and therefore cannot be obtained by minimizing any submodular auxiliary-variable function. A violating submodularity square for any proposed complements is constructible in polynomial bit time. This tests a new optimization bridge, rather than repeating basis restriction or independent-circuit assembly. The assigned exact-failure alternative is met, subject to fresh review; neither original M8 outcome is established.",
    "remaining_obligations": [
      "Construct a polynomially discoverable exact optimizer for joint physical detector branches beyond this failed auxiliary-cut representation. The new certificate rejects a representation; it does not optimize unrestricted inputs.",
      "Resolve unrestricted surviving odd cyclic core minima and establish physical-weight and nonboundary transport for any scalar bridge.",
      "Meet original M8 outcome A on every admitted input, including even orders, full gcd multiplicities, NoLogical, polynomial bit time and storage, and minimum physical witness recovery.",
      "Alternatively meet outcome B with a complete established-hard-source polynomial-size family-preserving reduction, both physical nonboundary threshold directions, exclusion of unintended smaller logicals, and connection to proved tractable regimes.",
      "Obtain fresh matching independent dual reviews of this complete candidate and summary before integration. No reviews or integration are claimed."
    ],
    "scope": "sublemma",
    "reviewed_source_run": "run-humo1h0e"
  },
  {
    "candidate_sha256": "f7255a7b9f2fe0a1d750954b6ced368aa7ca1a8841bc69eeb6c04a3d70f5530a",
    "proof_path": "docs/proof-792004a58845a696239d0bdc32a650fa48cc31ce8b74c62e970c71994193a67a.md",
    "claim": "New objective-specific reduction: minimum weight and an attaining original-coordinate word of any nonzero binary cyclic ideal reduce to ONE unpinned exact-value pricing query with exactly one negative coefficient and nearly uniform positive coefficients. For every admitted two-block CSS input, exact physical distance and a minimum logical witness reduce to at most TWO analogous queries on explicitly constructed marked linear codes. All coefficients have O(N+log N) bits; preprocessing and decoding are polynomial. This removes arbitrary successive pins and unrestricted signed objectives from these sufficient interfaces. It does not supply their pricing optimizer, and the marked physical codes need not be scalar cyclic ideals. Neither original M8 outcome is established.",
    "remaining_obligations": [
      "Construct a polynomial exact-value optimizer for the single-negative, nearly uniform objective (2) on unrestricted surviving odd cyclic ideals. Its time and storage remain unknown.",
      "Construct a polynomial optimizer for the two marked physical code queries, or prove another sufficient transport from a solved scalar interface. These marked codes are not generally scalar cyclic ideals.",
      "Establish actual tractable coverage beyond existing regimes; this conditional reduction does not establish a new polynomial regime.",
      "Close original M8 only with a uniform polynomial-bit-time and storage exact-distance/minimum-physical-witness algorithm for every admitted input, or a complete polynomial-size established-hard-source family-preserving reduction with both threshold directions, exclusion of unintended logicals, and connection to proved tractable regimes.",
      "Obtain matching fresh independent dual reviews of this complete candidate and summary before integration."
    ],
    "scope": "sublemma",
    "reviewed_source_run": "run-9pvywkq1"
  },
  {
    "candidate_sha256": "b5e9b15b20f12b833fac1581a6899ed314bd59426e03557a783c5375babfde46",
    "proof_path": "docs/proof-c7dc48dd71d69b4adc3edc36fc6c008d92277066d1dc61d0254c544c40591a2f.md",
    "claim": "Repaired Lane B exact-failure theorem. For every even L≥4, put N=L²+1, a=1+x and b=1+x^L. These are connected equal-positive-weight binary two-block recipes. Every nonempty affine nonboundary branch defined by detectors vanishing on the boundary space, under every full column basis of its joint constraint matrix, has an exact physical objective wt(c+Ty)+wt(y) with an uncancelled Fourier interaction of degree at least three. This survives coordinate complements and every permitted recipe presentation, including arbitrarily redundant detector descriptions. Certificate validation and extraction take O((N+Q+1)^6) bit time and O((N+Q+1)^4) bits of storage for an explicit proposal of Q bits. The sharper O((N+1)^6) time and O((N+1)^4) storage bounds apply to compact proposals containing at most two detector rows independent modulo the syndrome rows. No N-only processing bound is claimed for unrestricted redundant input. This excludes the specified purely quadratic representation search, not higher-order optimizers or other representations. Neither original M8 gate is met; M8 remains open.",
    "remaining_obligations": [
      "Construct an exact polynomial optimizer for surviving higher-order physical interactions, or a polynomially discoverable alternative representation with complete nonboundary coverage and minimum physical witness recovery.",
      "Resolve unrestricted surviving odd cyclic core minima in Lane A and prove physical-weight and nonboundary transport for any scalar bridge.",
      "Meet original M8 outcome A uniformly over every admitted order, span and weight, including full gcd multiplicities, NoLogical, polynomial bit time and storage, representation discovery and minimum logical witnesses.",
      "Alternatively establish original outcome B through a complete polynomial-size established-hard-source family-preserving reduction, both physical nonboundary threshold directions, exclusion of unintended smaller logicals and connection to proved tractable regimes.",
      "Obtain two new independent reviews matching this revised candidate and its summary before integration. No fresh reviews or integration are claimed."
    ],
    "scope": "sublemma",
    "reviewed_source_run": "run-9pvywkq1"
  },
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
  }
]

## Previous batch failures — do not repeat unchanged

[]
