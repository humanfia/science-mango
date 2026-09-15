# M6 round 2: arbitrary-order exact distance reduction
Status: unreviewed route proposal, 2026-09-15.
The user asks to continue M6 with the M5 harness and receive five-minute updates.

## Existing results and scope
M5 is adopted at arithmetic-workflow strength. Read M6_INPUT_M5_PROOF_20260915.md
and M6_INPUT_M5_DISTANCE_20260915.md, copied from dd809848.
Round 1 established a scoped fixed-support eventual distance theorem with a
finite optimizer; see M6_STAGE1_REVIEWED_PROOF_20260915.md. Its unchanged
composition received two independent no_gap_found reviews in run-ilz5dy5m.
Review votes are not mathematical premises; check any invoked argument.
Do not reopen SELF or birth_lift. Do not merely reprove stabilization.

The next target is an exact reduction for all allowed orders N>R,
including N<=RD. Allow supports to vary between inputs. Dependence exponential
in support span is permitted and must be explicit. Do not claim a small
invariant predictor or M7 completion.

## Candidate route to independently prove, repair or falsify
Let a,b be nonzero binary ordinary polynomials with supports in [0,R],
R=max(deg a,deg b)<N, and constant terms one after anchoring.
F=gcd(a,b,x^N+1), f=deg F. Let B=row(H_X) and C=ker(H_Z).
First establish dim B=N-f with full multiplicities. B is contained in C.

Construct a polynomial transfer matrix T(y) with 2^R memory states.
A state holds the last R bits of a cyclic input h; an edge appends t in {0,1},
shifts memory, and is weighted by y^e, where e is the sum of the two
binary convolution output bits of a*h,b*h at that step.
Entries sum edge weights when multiple edges have the same endpoints,
including R=0. Check orientation conventions and cyclic boundaries exactly.

Proposed identities:
    W(y)=trace(T(y)^N)=sum_{h in GF(2)^N} y^{wt(ah)+wt(bh)}
    E_B(y)=2^(-f) W(y)
The normalization is essential: every boundary has 2^f preimages.

Use binary character orthogonality to prove the dual weight enumerator
identity from scratch. Coordinate inversion and block exchange identify
row(H_Z) with a weight-preserving permutation of B. Therefore
    E_C(y)=2^(-N) trace(U(y)^N)
where U has the same memory transitions but edge weight
(1+y)^(2-e)*(1-y)^e.
Consequently
    Q(y)=2^(-N) trace(U(y)^N) - 2^(-f) trace(T(y)^N)
should count physical X cycles outside B at each weight.
If f>0, the first positive coefficient gives d_X=d_Z=d.
If f=0, Q is identically zero and there is no logical distance.

Check the signs, powers of two, even N, repeated factors, R=0,
nonnegative coefficient meaning, and total counts. This is a candidate,
not a premise. Prove a precise algorithm and bit-complexity bound:
sparse transfer iteration separately for each initial memory state suggests
O(N^2*4^R) coefficient arithmetic, polynomial in N when R is fixed.
Exponential dependence on R means this is not an efficient general
all-support solution. No raw support-pair enumeration is needed.
Avoid any claim of practical superiority without evidence.

If possible, extend to coordinate restrictions and a reconstructible minimum
logical witness using exact completion counts and bit decisions. Uniform
weight enumerator permutation symmetry is insufficient by itself for
coordinate-pinned formulas: explicitly preserve the H_X/H_Z orientation.
Do not smuggle an exponential raw physical-vector search into a claimed
polynomial-in-N witness constructor.

## Required result
Provide a self-contained symbolic theorem, explicit coefficient algorithm,
scope, falsifiers and independent full reviews of the unchanged composition.
A useful exact algorithm can satisfy the roadmap's certified-reduction route;
distinguish that from a concise predictor, efficient arbitrary-span method,
M7 universal optimum selection, or Lean certification.
Finite numerical evidence alone cannot prove the all-order identities.
