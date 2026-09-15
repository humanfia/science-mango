# Original M6: exact distance reduction and acceptance proof

The claim and argument below are extracted verbatim from the frozen candidate. The two subsequent full-scope reviews report no_gap_found for the same candidate hash. Author-time statements that execution and dual review remain outstanding are historical; current workflow results are recorded separately in integration-decision.json and verification-replay.json. This is a natural-language symbolic theorem, not Lean certification.

## Claim

Original M6 is satisfied at scoped symbolic exact-reduction strength. For anchored a,b∈GF(2)[x] with equal positive support weight, R=max(deg a,deg b)<N, and gcd(N,supp(a),supp(b))=1, the transfer algorithm below computes exact quantum distance and reconstructs a minimum logical witness whenever F=gcd(a,b,x^N+1) has positive degree; otherwise it reports no logical distance. It applies at every N>R, including even N with repeated factors. In the stated indexed-array bit model, distance takes O(N³4^R) work, witness reconstruction O(N⁴4^R), and storage O(N²2^R). This is polynomial in N at fixed presentation span R. Static inspection establishes correspondence of the supplied Python functions on valid inputs with default pin orientation. Fresh execution and fresh independent dual reviews were not performed under this turn’s restrictions. Practical superiority, efficient arbitrary-span computation, M7, and quantum-code classification are outside this claim.

## Argument (verbatim)

1. Original acceptance gate and integration.
Roadmap §10 permits “a certified reduction that makes exact distance cheaper”; §12 accepts M6 through “Proved domain or frozen held-out predictive success”. The theorem supplies the reduction and proved-domain alternatives. Section 11 distinguishes symbolic validity throughout stated hypotheses from finite certificates confined to their frozen domains. A held-out predictor is therefore not required for this symbolic route.

The stage-2 theorem and supplied closure draft overlap mathematically. The latter adds the acceptance comparison and implementation accounting; it does not enlarge the theorem’s parameter domain. Their common proof is composed below without using earlier review verdicts, M5, SELF, stage-1 stabilization, or numerical catalogue distances as premises. All eight cited files were read fully, and their locally computed SHA-256 values matched _snapshot.json. The seven source dependencies declared by the supplied closure draft are retained. The C105 documents report replacement of revoked lower certificates and three maximizers; the roadmap’s historical five-maximizer assertion is not used. No independent certification of those numerical catalogue claims is asserted here.

2. Physical cycle and boundary spaces, including multiplicities.
Set M=x^N+1 and S=GF(2)[x]/(M). Represent each physical block by its N coefficients. With the stipulated plus-offset circulant rows, X boundaries are B=im L, where L(h)=(ah,bh). The H_Z syndrome of (u,v) is bu+av, so C=ker[(u,v)↦bu+av]. Commutativity and characteristic two give B⊆C.

Write F=gcd(a,b,M), f=deg F and M=FK. A polynomial Bézout identity F=pa+qb+rM proves ker L=ker multiplication by F: vanishing under a and b implies vanishing under F, and the converse follows from F dividing a,b. For the representative H of degree less than N, M divides FH exactly when K divides H, by cancellation in GF(2)[x]. These representatives are precisely Kt with deg t<f. Hence |ker L|=2^f, dim B=N−f, and each boundary has 2^f preimages. This uses full polynomial multiplicities and works unchanged at even N.

Define J(u,v)_i=(v_{−i},u_{−i}), with indices modulo N. This orthogonal, weight-preserving involution sends row i of H_X to row −i of H_Z. Thus B_Z=JB, C=(JB)^⊥, dim C=N+f, and J maps the X cycle/boundary pair to the Z pair. Consequently k=2f and the two type distances agree whenever logicals exist.

3. Exact indexed transfer construction.
A memory state m=(m_1,…,m_R) stores preceding input bits, most recent first. Appending t∈{0,1} sends it to (t,m_1,…,m_{R−1}) with outputs α=a_0t+Σa_jm_j and β=b_0t+Σb_jm_j in GF(2). At R=0 keep two distinct labeled loops on the single empty state.

An indexed cyclic input h determines memory m_{i,j}=h_{i−j}. Conversely, periodically extend a closed length-N labeled walk; iterating its shift rule backward j steps forces this same formula. These constructions are inverse, and its outputs are (ah)_i,(bh)_i. Thus closed walks count indexed inputs, without rotation division. For any layer-dependent weights, define a matrix entry as the sum over all labeled edges with its endpoints. Expanding the trace of the ordered matrix product counts exactly these walks, including parallel loops.

Give T an edge weight y^(α+β), where the exponent is an ordinary integer. Then tr(T^N)=Σ_h y^wt(L(h)), so E_B=2^(−f)tr(T^N).

4. Character formula and exact logical enumerator.
For a binary subspace D, Σ_{q∈D}(−1)^(q·z) equals |D| on D^⊥ and zero elsewhere. Outside D^⊥, translation by a q_0 with q_0·z=1 pairs opposite signs. Summing against y^wt(z) and factoring over coordinates yields E_{D^⊥}=|D|^(−1)Σ_{q∈D}∏_j(1+(−1)^(q_j)y).

Take D=JB and parameterize q=JL(h). Each q has 2^f preimages and |D|=2^(N−f), giving input-sum normalization 2^(−N). Uniform coordinate factors are unchanged by J. Therefore, if U has edge weight (1+y)^(2−α−β)(1−y)^(α+β),
Q(y)=2^(−N)tr(U^N)−2^(−f)tr(T^N)=Σ_{z∈C\B}y^wt(z).

Both divisions are exact coefficientwise, despite signed character intermediates. Final coefficients are nonnegative integers, Q(0)=0 and Q(1)=2^(N+f)−2^(N−f). If f=0, B=C and Q=0, so no logical distance exists. Otherwise its first positive coefficient gives d_X=d_Z. Any nontrivial CSS logical Pauli has a nonboundary X or Z component with support contained in its Pauli support; a pure minimum logical attains this bound. The extracted value is therefore quantum distance, with all smaller weights excluded.

5. Pinned enumerators and constructive witness.
For each physical coordinate q choose A_q∈{{0,1},{0},{1}}. Define b_q(s)=1_{s∈A_q}y^s and c_q(s)=Σ_{z∈A_q}(−1)^(sz)y^z. At layer i use boundary weight b_{L,i}(α)b_{R,i}(β) and character weight c_{R,−i}(α)c_{L,−i}(β). Denote the resulting matrices T_i^P,U_i^P.

All preimages of a boundary have identical pin acceptance and physical weight. Restricting the preceding character sum coordinate by coordinate gives
B_P=2^(−f)tr(∏_i T_i^P), C_P=2^(−N)tr(∏_i U_i^P), Q_P=C_P−B_P.
The swap and inversion are necessary: α at layer i occupies (R,−i) after J, while β occupies (L,−i). Thus Q_P counts precisely pinned nonboundary cycles, including the weight of pinned ones.

For every free coordinate q, Q_P=Q_{P,q=0}+Q_{P,q=1}. Starting with positive [y^d]Q, visit all 2N coordinates, tentatively pinning each to zero. Keep zero when the new coefficient is positive; otherwise choose one. The partition identity preserves a positive number of weight-d completions. Fully assigned pins specify exactly one vector, proving its weight, zero syndrome, and nonboundary status. This needs at most 2N further paired trace queries. Applying J supplies a Z witness.

6. Reproducible finite algorithm and resource bound.
Put s=2^R. For each initial state separately, initialize its polynomial to 1 and all others to zero. At each layer, propagate every state polynomial along both labeled edges, multiplying by that edge’s degree-at-most-two polynomial and adding into its successor. After N layers add the initial-state entry to the trace accumulator. This is direct expansion of the ordered matrix product. Coefficient arrays through degree 2N retain every term.

There are s starts, N layers, at most 2s edges per layer and O(N) coefficients per polynomial. Each edge multiplication has at most three small coefficients. A trace therefore uses O(N²s²) coefficient operations. Each edge polynomial has coefficient ℓ1 norm at most four; at depth i there are at most 2^i paths from a start. Absolute contributions and partial accumulations are bounded by 8^i, and the total trace by s8^N. Since R<N, signed integers require O(N) bits. Addresses use O(R+log(N+2)) bits, also O(N). Charging arithmetic and address manipulation gives O(N³s²) bit work per trace in an indexed-array RAM model.

Two reusable layers use O(Ns) coefficients of O(N) bits, hence O(N²s) storage. Transitions, accumulators and pins fit that bound. Binary polynomial Euclid takes a conservative O(N³) bit bound; exact power-of-two divisions and preprocessing are absorbed. Constantly many traces yield distance, and O(N) queries yield a witness, proving the stated bounds.

For fixed R, both N³4^R/4^N and N⁴4^R/4^N tend to zero. Exhaustive physical-vector scanning visits 4^N vectors. This establishes an asymptotically cheaper exact method on an unbounded declared domain. That domain contains nontrivial fixed-span families: a=b=1+x+x², R=2 and every N>2 divisible by 3 satisfy connectivity and have F=1+x+x². The comparison establishes neither practical superiority over existing solvers nor efficiency when R grows with N. No original M6 clause requires those stronger properties.

7. Static executable correspondence.
The supplied script represents binary polynomials as integers. remainder cancels leading terms and gcd performs Euclid; counts computes F from (1<<N)|1, retaining multiplicities. Memory bit zero is the most recent bit. window=(memory<<1)|bit places input and memory at the required offsets; masking by states−1 gives the successor, and parity against a,b gives α,β. Both labeled edges remain separate list entries at R=0.

factor implements exactly b_q and c_q, and product multiplies them. Default character positions N+(-i)%N and (-i)%N implement the required swapped, inverted coordinates. wrong_orientation=True is a deliberate corruption control and is excluded from production correctness. The current/following recurrence propagates every reachable polynomial; setdefault accumulates coincident destinations, and current.get(start,[]) closes the walk. Layer arrays have sufficient degree. counts checks divisibility before signed integer division, then subtracts the boundary enumerator. Exactness, rather than rounding behavior, justifies these divisions.

distance_witness selects the first nonzero Q coefficient and follows the pinned algorithm. Nonnegativity makes its zero test equivalent to testing whether a completion survives. The final weight assertion alone is not a standalone membership certificate, but the proved pin invariant establishes membership and nonboundary status. Q=0 returns distance=None and witness=None.

The interface permits anchored supports without checking equal weights or connectivity. The algebraic identities remain valid for those broader controls, while the declared M6 claim retains both restrictions. Correctness concerns valid integer inputs and documented pin values, not arbitrary Python objects.

8. Implementation resources and evidence boundary.
The code uses dictionaries instead of indexed state arrays and materializes positional weights for all N layers. This is O(Ns) constant-degree polynomial objects, with O(Ns(R+log(N+2))) bits of keys, references and indexing in a bit-addressed object model. Two polynomial layers dominate at O(N²s) bits. Eager evaluation of setdefault’s zero-array argument adds O(N) initialization per processed edge, absorbed by the coefficient-loop bound, though potentially expensive in practice.

The deterministic O(N³4^R) theorem is for the explicit indexed-array algorithm. Applying that timing bound directly to Python dictionaries requires an amortized access assumption; it is not an unconditional interpreter-performance guarantee. Even a conservative O(s)-probe dictionary model adds at most a factor s, retaining polynomial dependence on N at fixed R. No measured performance claim is supported by the report.

matrix_sets constructs physical H_X rows with plus offsets and H_Z rows with minus offsets and block exchange. Distinct residues and disjoint blocks make its sums of bitmasks valid. It independently enumerates the boundary span and every vector satisfying the physical syndrome checks. histogram checks pins and physical weight directly. validate compares all three enumerators, distance, and reconstructed witness membership. Its small equal-weight domain includes disconnected recipes, which are algebraic controls rather than additional connected-family coverage.

The stored report records 99 recipes, 790 pinned comparisons and 49 nontrivial witness reconstructions, including empty memory, no logicals, repeated factors, and wrong pin orientation. These are recorded finite results, not freshly reproduced checks or uniform proof premises. The entire implementation was inspected; no research code was executed.

9. Symmetry, edge cases and falsifiers.
Independent translations a'=x^ra,b'=x^sb induce P(u,v)=(x^ru,x^sv), sending boundaries to boundaries and syndrome to x^(r+s)(bu+av). A common unit multiplier induces the coefficient permutation x^i↦x^(ui), and block exchange swaps supports and physical blocks. Each preserves weight and the cycle/boundary pair. The exact recipe group is unchanged. Span depends on presentation; no module shear is treated as a weight isometry, and recipe classes are not asserted to be inequivalent quantum codes.

For R=0, a=b=1. Summing both loops gives T=1+y² and U=2(1+y²), so both normalized enumerators equal (1+y²)^N and Q=0. Connectivity restricts this presentation to N=1. Generally the constant normalized coefficients are one, and total counts agree with the dimensions derived above.

Falsifiers include incorrect boundary-fiber size, failure of the indexed-walk correspondence, nonintegral normalization, negative Q_P coefficients, wrong constant or total counts, nonzero Q at f=0, failure of pin partition, or a reconstructed witness with wrong weight, nonzero syndrome or stabilizer membership. The symbolic argument excludes these within its hypotheses; they remain useful executable corruption targets.

10. Closure decision.
No precise original M6 mathematical clause remains unmet at this scoped exact-reduction strength. The proof covers every allowed order without a stabilization cutoff and constructs matching upper witnesses while its enumerator excludes smaller logicals. Fresh independent dual reviews and executable reproduction remain workflow work outside this claim; neither can be truthfully reported as completed under the frozen no-agent, no-execution policy. This assessment supplies one independent static reading, not two independent reviews.
