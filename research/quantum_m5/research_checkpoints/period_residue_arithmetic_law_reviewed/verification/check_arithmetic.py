"""Independent small-parameter falsifier checks; not premises of the theorem."""
from functools import lru_cache
from itertools import combinations, product
from collections import Counter
from math import gcd, comb
import json
from pathlib import Path


def rem(a,b):
    while a and a.bit_length() >= b.bit_length():
        a ^= b << (a.bit_length()-b.bit_length())
    return a

def mul(a,b):
    z=0
    while b:
        if b&1: z ^= a
        a <<= 1; b >>= 1
    return z

def div(a,b):
    q=0
    while a and a.bit_length() >= b.bit_length():
        s=a.bit_length()-b.bit_length(); q ^= 1<<s; a ^= b<<s
    assert not a
    return q

def pgcd(a,b):
    while b: a,b=b,rem(a,b)
    return a

def poly(xs):
    r=0
    for x in xs: r ^= 1<<x
    return r

@lru_cache(None)
def factors(a):
    out=[]; p=3
    while a != 1 and 2*(p.bit_length()-1) <= a.bit_length()-1:
        e=0
        while rem(a,p)==0: a=div(a,p); e+=1
        if e: out.append((p,e))
        p += 2
    if a!=1: out.append((a,1))
    return tuple(out)

@lru_cache(None)
def divisors(a):
    out=[1]
    for p,e in factors(a):
        old=out[:]; pp=1
        for _ in range(e):
            pp=mul(pp,p); out += [mul(x,pp) for x in old]
    return tuple(sorted(out))

@lru_cache(None)
def ie(a):
    out=[(1,1)]
    for p,_ in factors(a): out += [(mul(h,p),-s) for h,s in out[:]]
    return tuple(out)

def idivs(n): return [d for d in range(1,n+1) if n%d==0]
def mu(n):
    ans=1; p=2
    while p*p<=n:
        if n%p==0:
            n//=p; ans=-ans
            if n%p==0: return 0
        while n%p==0: n//=p
        p+=1
    return -ans if n>1 else ans

def choose(n,k): return comb(n,k) if 0<=k<=n else 0

@lru_cache(None)
def ncount(P,W,k,z):
    if k<0 or k>len(W): return 0
    if P==1: return choose(len(W),k)
    z=rem(z,P); vals=[rem(1<<s,P) for s in W]; D=P.bit_length()-1
    total=0
    for lam in range(1<<D):
        neg=sum((lam&v).bit_count()%2 for v in vals); pos=len(W)-neg
        c=sum((-1)**j*choose(neg,j)*choose(pos,k-j) for j in range(k+1))
        total+=(-1)**((lam&z).bit_count()%2)*c
    assert total%(1<<D)==0
    return total//(1<<D)

def completion(N,w,F,A=(0,),B=(0,),WA=None,WB=None):
    M=(1<<N)|1
    if w>N or rem(M,F): return 0
    if WA is None: WA=tuple(range(1,N))
    if WB is None: WB=tuple(range(1,N))
    g=gcd(N,*A,*B); total=0
    for d in idivs(g):
        md=mu(d)
        if not md: continue
        va=tuple(s for s in WA if s%d==0); vb=tuple(s for s in WB if s%d==0)
        for H,sgn in ie(div(M,F)):
            P=mul(F,H)
            total+=md*sgn*ncount(P,va,w-len(A),poly(A))*ncount(P,vb,w-len(B),poly(B))
    assert total>=0
    return total

def recover(N,w,F):
    A=(0,); B=(0,); WA=tuple(range(1,N)); WB=WA
    assert completion(N,w,F)>0
    for block in range(2):
        for s in range(1,N):
            if block==0:
                WA=WA[1:]
                if completion(N,w,F,A,B,WA,WB)==0: A+= (s,)
            else:
                WB=WB[1:]
                if completion(N,w,F,A,B,WA,WB)==0: B+= (s,)
            assert completion(N,w,F,A,B,WA,WB)>0
    assert len(A)==len(B)==w and gcd(N,*A,*B)==1
    assert pgcd(pgcd(poly(A),poly(B)),(1<<N)|1)==F
    return A,B

@lru_cache(None)
def rcount(P,T,d,k,z):
    if P==1: return (T//d)**k
    D=P.bit_length()-1; z=rem(z,P); vals=[rem(1<<s,P) for s in range(0,T,d)]
    total=0
    for lam in range(1<<D):
        c=sum((-1)**((lam&v).bit_count()%2) for v in vals)
        total+=(-1)**((lam&z).bit_count()%2)*c**k
    assert total%(1<<D)==0
    return total//(1<<D)

def global_count(T,w,F):
    return sum(mu(d)*sgn*rcount(mul(F,H),T,d,w-1,1)**2 for d in idivs(T) for H,sgn in ie(div((1<<T)|1,F)))

def residue_completion(T,w,F,A=(0,),B=(0,)):
    return sum(mu(d)*sgn*rcount(mul(F,H),T,d,w-len(A),poly(A))*rcount(mul(F,H),T,d,w-len(B),poly(B)) for d in idivs(gcd(T,*A,*B)) for H,sgn in ie(div((1<<T)|1,F)))

def recover_residues(T,w,F):
    A=(0,); B=(0,)
    assert residue_completion(T,w,F)>0
    for block in range(2):
        for _ in range(w-1):
            for r in range(T):
                aa=A+(r,) if block==0 else A
                bb=B+(r,) if block==1 else B
                if residue_completion(T,w,F,aa,bb)>0:
                    A,B=aa,bb; break
            else: raise AssertionError('no positive residue branch')
    assert gcd(T,*A,*B)==1 and pgcd(pgcd(poly(A),poly(B)),(1<<T)|1)==F
    return A,B

def period(G):
    if G==1: return 1
    x=rem(2,G); y=x; E=1
    while y!=1:
        y=rem(y<<1,G); E+=1
    return E

def pack_and_lift(T,w,F,A,B):
    def pack(R):
        seen=Counter(); out=[]
        for r in R: out.append(r+seen[r]*T); seen[r]+=1
        return out
    a,b=pack(A),pack(B); idx=next(i for i,e in enumerate(a) if e>0); e=a[idx]
    delta=gcd(*(a[:idx]+a[idx+1:]+b)); k=w
    while gcd(delta,e+k*T)!=1: k+=1
    assert k<=w+delta-1
    a[idx]+=k*T; L=w*T*(T+2)
    assert max(a+b)<L and gcd(*a,*b)==1
    G=pgcd(poly(a),poly(b)); E=period(G)
    assert E<=2**(w*T-1) and E%T==0
    N=T+max(0,(L-T+E-1)//E)*E
    assert N<L+2**(w*T) and len(set(a))==len(set(b))==w
    # Reduce x^N modulo G without constructing a huge polynomial.
    y=rem(1,G); x=rem(2,G); n=N
    while n:
        if n&1: y=rem(mul(y,x),G)
        x=rem(mul(x,x),G); n//=2
    assert pgcd(G,y^1)==F and gcd(N,*a,*b)==1
    return {'T':T,'w':w,'F':F,'A':a,'B':b,'G':G,'E':E,'N':N,'bound':L+2**(w*T)}

def main():
    counts=0; witnesses=0; pairs=0; residues=0; packs=[]; examples=[]
    for N in range(1,9):
        M=(1<<N)|1
        for w in range(1,N+1):
            supports=[(0,)+c for c in combinations(range(1,N),w-1)]; brute=Counter()
            for A,B in product(supports,repeat=2):
                pairs+=1
                if gcd(N,*A,*B)==1: brute[pgcd(pgcd(poly(A),poly(B)),M)]+=1
            for F in divisors(M):
                C=completion(N,w,F); assert C==brute[F],(N,w,F,C,brute[F]); counts+=1
                if C:
                    recover(N,w,F); witnesses+=1
        print('finite order',N,'passed',flush=True)
    for T in range(1,7):
        fs=[F for F in divisors((1<<T)|1) if period(F)==T]
        for w in range(2,5):
            tuples=[(0,)+r for r in product(range(T),repeat=w-1)]; brute=Counter(); first={}
            for A,B in product(tuples,repeat=2):
                if gcd(T,*A,*B)!=1: continue
                F=pgcd(pgcd(poly(A),poly(B)),(1<<T)|1); brute[F]+=1; first.setdefault(F,(A,B))
            for F in fs:
                value=global_count(T,w,F); assert value==brute[F],(T,w,F,value,brute[F]); residues+=1
                if value:
                    recovered=recover_residues(T,w,F)
                    packs.append(pack_and_lift(T,w,F,*recovered))
                    pack_and_lift(T,w,F,*first[F])
        print('residue period',T,'passed',flush=True)
    result={'finite_order_formula_cases':counts,'brute_support_pairs':pairs,'conditional_witnesses':witnesses,'period_residue_formula_cases':residues,'packed_progression_witnesses':len(packs),'examples':packs,'status':'all_passed','proof_status':'finite falsifier checks only'}
    Path(__file__).with_name('test-results.json').write_text(json.dumps(result,indent=2)+'\n'); print(json.dumps({k:v for k,v in result.items() if k!='examples'}))
if __name__=='__main__': main()
