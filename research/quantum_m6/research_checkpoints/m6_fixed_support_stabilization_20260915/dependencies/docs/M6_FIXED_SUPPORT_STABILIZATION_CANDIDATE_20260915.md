# M6: eventual fixed-support distance candidate
Status: unreviewed candidate for the M5 quantum_humanize harness. 2026-09-15.

## Current assignment
The user requests starting M6 using the M5 harness. M5 is adopted at
arithmetic-workflow strength in publication dd809848. Read the exact copies
M6_INPUT_M5_PROOF_20260915.md and M6_INPUT_M5_DISTANCE_20260915.md.
Historical SELF/birth_lift task prose does not reopen M5. M6 remains open.
Independently verify, repair or replace the following route. It is not an
accepted premise. Preserve the distinction between a scoped M6 theorem
and all-support distance classification or M7.

## Proposed theorem
Over GF(2), fix nonzero ordinary polynomials a,b with constant term 1.
Let R=max(deg a,deg b), G=gcd(a,b), a0=a/G, b0=b/G,
D=wt(a0)+wt(b0), and L=R(D-1).
Fix nonconstant F with F(0)=1 and consider every N>R satisfying
gcd(G,x^N+1)=F. Repeated factors and even N are included.
Equal support weights and connectivity can be imposed to restrict to the
declared recipe family; the proposed argument does not require them.

For every such N>RD the proposed exact law is

    d_X(N)=d_Z(N)=delta(a,b,F)
    delta = min {wt(a0*c)+wt(b0*c): deg c<=L, F does not divide c}.

The minimum is finite and <=D since c=1 is allowed. It depends on fixed
supports and F, not on N. Thus every M5 fixed-support infinite progression
with nontrivial F eventually has constant distance. No monotonicity below
RD, equality delta=D, or common constant across different supports is claimed.

## Proposed proof to audit
Use R_N=GF(2)[x]/(x^N+1) with the distance_m5.py convention:
X cycles satisfy bu+av=0 and X boundaries are (ah,bh).

1. Bezout for coprime a0,b0 makes c -> (a0*c,b0*c) injective over R_N.
Such a cycle is a boundary iff c=G*h in R_N, equivalent to F dividing
its representative since (G,x^N+1)=(F). This uses no squarefreeness.
The choice c=1 proves d_X<=D and supplies a nontrivial logical.

2. For a cycle of weight t, form a graph on occupied physical qubits,
joining two when their syndrome contributions share a check position.
Left qubit i contributes at i+supp(b), right qubit j at j+supp(a).
Different components share no checks, so each separately is a cycle.
If their sum is nontrivial, at least one component is nontrivial since
boundaries form a linear subspace.

3. Lift a connected component on s<=t vertices to integer coordinates
along a spanning tree. Every tree edge has a displacement in [-R,R],
obtained from the shared check. Any two lifted coordinates differ by at
most R(s-1), using their tree path. Shift the minimum to zero.
The resulting U,V have degree <=R(s-1), and bU+aV has support in [0,Rs].
It reduces to zero modulo x^N+1. If N>Rs its degree is <N, hence it is
identically zero. No consistency assumption for non-tree edges is needed:
vanishing cyclic syndrome and the degree bound suffice.

4. Coprimality over GF(2)[x] now gives (U,V)=(a0*c,b0*c),
with deg c<=R(s-1)<=L. The lift followed by common cyclic translation
preserves the original component and nontriviality, so F does not divide c.
Apply to a minimum logical cycle, of weight t<=D. When N>RD this yields
delta<=d_X(N).

5. Conversely any c in the finite displayed domain has output degrees
<=L+R=RD<N. Polynomial weight equals cyclic weight, and step 1 proves
nontriviality. Hence d_X(N)<=delta. Coordinate inversion plus block
exchange maps H_X to H_Z and preserves weight, proving d_Z=d_X.

## Exact computational reduction
Compute the finite minimum by convolutional dynamic programming. Read bits
c_i for i=0,...,L. Keep the last r bits, r=max(deg a0,deg b0), and the
accumulated remainder sum c_i*x^i mod F. Each step contributes the two
output coefficient weights. Append r forced zero bits to flush the memory.
Minimize over final nonzero remainders. Same memory and remainder at the
same time give identical future costs. Prove the recurrence and validate
independently against small cyclic matrices. This is independent of N,
but exponential dependence on span and deg F is permitted and must be stated.

## Falsifiers and evidence boundary
A qualifying N>RD whose exact distance differs from delta; a nonboundary
component failing to unwrap; or failure of the F-divisibility criterion
with repeated factors would falsify a claimed step.
Below-threshold differences are expected: a=1+x^3,b=1+x has D=4 but N=6
has d=2 in the supplied report. F=1 means no logical distance.
Do not promote finite tests or review votes to a symbolic proof.
Obtain fresh independent reviews of the unchanged final composition and
retain all gaps. A scoped result does not solve the entire roadmap.
