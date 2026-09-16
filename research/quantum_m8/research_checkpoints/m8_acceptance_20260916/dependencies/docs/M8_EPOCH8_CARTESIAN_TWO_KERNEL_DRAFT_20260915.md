# Two arbitrary Cartesian kernels: new controller draft

2026-09-15. **UNREVIEWED; outside epoch 7 frozen inputs; M8 OPEN.**

## Domain and claimed distance

Let N=mq with m,q>=2 coprime. After independent block translations and
possibly a block swap, suppose a=A(x^q), b=B(x^m), deg A<m, deg B<q.
Retain the original connectedness and equal positive support weights.
No auxiliary simple-root or repetition-kernel hypothesis is imposed.
Let P be cyclic multiplication by A on V=F2^m, and Q multiplication by B
on W=F2^q. Write fP=dim ker P, fQ=dim ker Q.

If either kernel dimension is zero, there are no logicals. Otherwise the
candidate exact physical distance is

    d = min(d(ker P), d(ker Q)).

The coordinate permutation (r,s)->qr+ms mod N identifies the physical
coefficient space with V tensor W. On this space P and Q act in separate
directions. Boundaries are (Ph,Qh), cycles satisfy Qu+Pv=0.

## Algebra and exact lower bound

The boundary map has kernel ker P tensor ker Q: intersecting
ker(P tensor I)=ker P tensor W and ker(I tensor Q)=V tensor ker Q
gives that intersection, for example by choosing bases extending the two
kernels. Its rank is N-fP*fQ. The adopted full-gcd rank identity therefore
gives deg gcd(a,b,x^N+1)=fP*fQ, with full repeated multiplicities.
The physical logical dimension is 2*fP*fQ. This is a degree identity,
not a proposed equality of the full gcd with a source gcd polynomial.

For a cycle (u,v), let pi:W->W/im Q be the quotient map. Applying
I tensor pi to the cycle relation shows

    (P tensor I)(I tensor pi)v=0.

If (I tensor pi)v is nonzero, some linear functional ell on W/im Q
extracts a nonzero z=(I tensor ell*pi)v in ker P. Each nonzero coordinate
of z requires at least one nonzero coefficient in the corresponding row
of v, so wt(v)>=wt(z)>=d(ker P). All boundaries have this projection zero.

If that projection is zero, v belongs to V tensor im Q. Choose h with
Qh=v and add its boundary. The cycle becomes (u',0), with
u'=u+Ph in V tensor ker Q. It is a boundary exactly when
u' belongs to im P tensor ker Q: boundaries with second component zero
have h0 in V tensor ker Q and first component Ph0, giving exactly this
subspace. If the cycle is nonboundary, its image in
(V/im P) tensor ker Q is nonzero. Some functional alpha on V/im P
therefore extracts a nonzero y=(alpha*piP tensor I)u' in ker Q.
Since alpha*piP annihilates P, the same y is extracted from the ORIGINAL
u. Thus wt(u)>=wt(y)>=d(ker Q). No weight-preserving boundary addition
was assumed. Every nonboundary cycle consequently has weight at least
the claimed minimum.

## Attaining physical witnesses

When fQ>0, im Q is proper. At least one coordinate unit e_s is outside
im Q, because all such units span W. For a minimum nonzero z in ker P,
(0,z tensor e_s) is a cycle, its quotient projection is nonzero, and it
has weight d(ker P). Similarly choose a unit e_r outside im P; if y is
a minimum nonzero word in ker Q, (e_r tensor y,0) is a nonboundary
cycle of weight d(ker Q). Testing units against image bases is polynomial.
CRT embedding and undoing recorded recipe transformations return actual
physical witnesses. The adopted pure/mixed CSS argument makes this pure
minimum the full quantum minimum. No transpose-distance oracle is used.

## A charged polynomial regime

Recognize the additional conditions

    2^fP <= (N+1)^2 and 2^fQ <= (N+1)^2.

Compute source kernels by binary elimination and enumerate their basis
combinations by Gray traversal, retaining each minimum nonzero word.
There are at most 2(N+1)^2 visits of words of length at most N, with
polynomial preprocessing and storage. Thus exact source minima and their
attaining words are charged polynomial work; they are not hidden oracles.
The full physical gcd is computed independently, retaining multiplicities.

Recognition can enumerate m=2,...,N-1, retain divisors q=N/m>=2 with
gcd(m,q)=1, and try both orientations. In each block translate any chosen
support point to zero. Check first support differences divisible by q
and second by m; divide exponents to recover A,B. An alternative anchor
merely rotates the corresponding source polynomial, preserving its kernel
dimension and minimum. Common unit multipliers preserve both support
cosets and act as unit coordinate permutations on each source. Hence this
recognition includes the entire declared recipe orbit. Testing all divisor
candidates costs polynomial time in EXPLICIT N, not in log N.

For each recognized form, compute fP,fQ and apply the budget tests BEFORE
enumerating either kernel. The first form passing both budgets suffices.
If no form passes, return Unsupported, never a guessed distance. A full
gcd of one allows the global NoLogical return before recognition. A very
conservative O((N+1)^7) bit time and O((N+1)^4) storage charge all divisor
scans, elimination, explicit source enumeration and witness verification.

The earlier power-of-two/simple-root branch is the case ker Q is
repetition and fQ=1. The weight-four Hamming/repetition family is included.
This draft does not establish strict separation from every previously
proved regime. Most inputs need not have the Cartesian form or meet the
two budgets. It does not settle M8 or generic computational hardness.

## Explicit odd-length, weight-four example family

For an optional concrete corollary use the separately UNREVIEWED source
lemma in weight_four_hamming_bridge.md: p=1+x^2+x^3+x^4 at m=7t,
t odd, has a four-dimensional kernel of minimum 3t. Set s=3t+2,
q=3s and B=1+x+x^3+x^4=(1+x)(1+x^3). Restrict odd t to t=1 mod 42.
Then t is coprime to 3, s is 5 mod 7 and gcd(t,s)=gcd(t,2)=1;
therefore gcd(7t,3s)=1. Both directions and N=mq are odd.

Since x^q+1 is square-free and 3 divides q, the full source gcd of B
with x^q+1 is x^3+1. The kernel of B equals that of 1+x^3 and consists
of all length-three patterns repeated s times. Its dimension is three
and minimum is s. The two-kernel theorem consequently gives

    N=21t(3t+2),  w=4,  f=12,  k=24,  d=min(3t,3t+2)=3t.

Connectedness follows from differences 2q,3q within a, giving q in the
generated subgroup, and the difference m within b; gcd(m,q)=1.
Both source budgets are constant. Thus this is an explicit unbounded
odd-length fixed-weight family with distance of order sqrt(N), subject
to fresh review of this draft AND the cited source lemma. It is outside
the power-of-two Cartesian recognition branch because N is odd.
For t>=43 its distance exceeds four. Any weight-two reference has rank
N-1, whereas D here has rank N-12; containment would be proper and supply
a weight-four nonboundary cycle, contradicting this exact distance.
This last exclusion invokes the separately reviewed containment theorem.
No all-weight-four complexity conclusion follows.

## Required fresh checks

Audit both quotient extraction cases, necessity and sufficiency of the
boundary criterion, full-gcd degree with repeated roots, physical witness
orientation and pin-free scope, recipe recognition and enumeration costs.
Any finite experiments are separate implementation checks, not premises.
