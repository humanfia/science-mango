#!/usr/bin/env python3
"""All-order transfer distance with coordinate-pinned witness reconstruction."""
import itertools
import json
from pathlib import Path

def remainder(a,b):
    while a and a.bit_length()>=b.bit_length():
        a ^= b << (a.bit_length()-b.bit_length())
    return a

def gcd(a,b):
    while b:
        a,b=b,remainder(a,b)
    return a

def product(p,q):
    out=[0]*(len(p)+len(q)-1)
    for i,x in enumerate(p):
        for j,y in enumerate(q):
            out[i+j]+=x*y
    return out

def factor(pin,bit,character):
    if character:
        return [int(pin!=1), (1 if bit==0 else -1)*int(pin!=0)]
    return [int(pin!=1),0] if bit==0 else [0,int(pin!=0)]

def trace(N,a,b,pins,character,wrong_orientation=False):
    R=max(a.bit_length(),b.bit_length())-1
    states=1<<R
    edges=[[] for _ in range(states)]
    for memory in range(states):
        for bit in (0,1):
            window=(memory<<1)|bit
            edges[memory].append((window&(states-1),(window&a).bit_count()%2,(window&b).bit_count()%2))
    weights=[]
    for i in range(N):
        if character and not wrong_orientation:
            left,right=N+(-i)%N,(-i)%N
        else:
            left,right=i,N+i
        weights.append([[product(factor(pins[left],u,character),factor(pins[right],v,character)) for _,u,v in es] for es in edges])
    total=[0]*(2*N+1)
    for start in range(states):
        current={start:[1]}
        for i in range(N):
            following={}
            for memory,poly in current.items():
                for index,(dest,_,_) in enumerate(edges[memory]):
                    w=weights[i][memory][index]
                    if not any(w):
                        continue
                    destpoly=following.setdefault(dest,[0]*(2*i+3))
                    for j,c in enumerate(poly):
                        if c:
                            for k,weight in enumerate(w):
                                destpoly[j+k]+=c*weight
            current=following
        for j,c in enumerate(current.get(start,[])):
            total[j]+=c
    return total

def counts(N,a,b,pins=None,wrong_orientation=False):
    if N<1 or min(a,b)<1 or not a&1 or not b&1 or max(a.bit_length(),b.bit_length())>N:
        raise ValueError('Require anchored nonempty supports of degree < N')
    pins=tuple([None]*(2*N) if pins is None else pins)
    if len(pins)!=2*N or any(p not in (None,0,1) for p in pins):
        raise ValueError('invalid pins')
    F=gcd(gcd(a,b),(1<<N)|1)
    f=F.bit_length()-1
    bt=trace(N,a,b,pins,False)
    ct=trace(N,a,b,pins,True,wrong_orientation)
    assert all(c%(1<<f)==0 for c in bt)
    assert all(c%(1<<N)==0 for c in ct)
    B=[c//(1<<f) for c in bt]
    C=[c//(1<<N) for c in ct]
    Q=[c-b for c,b in zip(C,B)]
    if not wrong_orientation:
        assert all(q>=0 for q in Q)
    return B,C,Q

def distance_witness(N,a,b):
    B,C,Q=counts(N,a,b)
    if not any(Q):
        return dict(distance=None,witness=None)
    d=next(i for i,q in enumerate(Q) if q)
    pins=[None]*(2*N)
    for i in range(2*N):
        pins[i]=0
        if counts(N,a,b,pins)[2][d]==0:
            pins[i]=1
    assert sum(pins)==d
    return dict(distance=d,witness=[i for i,p in enumerate(pins) if p])

# Independent physical-matrix enumeration: no transfer or polynomial gcd.
def matrix_sets(N,a,b):
    aa=[i for i in range(N) if a>>i&1]
    bb=[i for i in range(N) if b>>i&1]
    hx=[sum(1<<((i+j)%N) for j in aa)+sum(1<<(N+(i+j)%N) for j in bb) for i in range(N)]
    hz=[sum(1<<((i-j)%N) for j in bb)+sum(1<<(N+(i-j)%N) for j in aa) for i in range(N)]
    B={0}
    for row in hx:
        B|={v^row for v in tuple(B)}
    C={v for v in range(1<<(2*N)) if all((v&row).bit_count()%2==0 for row in hz)}
    assert B<=C
    return B,C

def histogram(vectors,N,pins):
    out=[0]*(2*N+1)
    for v in vectors:
        if all(p is None or ((v>>i)&1)==p for i,p in enumerate(pins)):
            out[v.bit_count()]+=1
    return out

def validate():
    recipes=pin_cases=logical_cases=0
    orientation_detected=False
    repeated_case=False
    for N in range(1,6):
        polys=list(range(1,1<<N,2))
        for a,b in itertools.product(polys,repeat=2):
            if a.bit_count()!=b.bit_count():
                continue
            B,C=matrix_sets(N,a,b)
            free=[None]*(2*N)
            patterns=[free]
            for position in {0,N,2*N-1}:
                for value in (0,1):
                    p=free.copy();p[position]=value; patterns.append(p)
            mixed=free.copy();mixed[0]=1;mixed[N]=0;patterns.append(mixed)
            for pins in patterns:
                expected=[histogram(V,N,pins) for V in (B,C,C-B)]
                actual=counts(N,a,b,pins)
                assert list(actual)==expected,(N,a,b,pins)
                pin_cases+=1
                if not orientation_detected and pins!=free:
                    wrong=counts(N,a,b,pins,wrong_orientation=True)
                    orientation_detected=(wrong[1]!=expected[1])
            result=distance_witness(N,a,b)
            exact=min((v.bit_count() for v in C-B),default=None)
            assert result['distance']==exact
            if exact is not None:
                v=sum(1<<i for i in result['witness'])
                assert v in C-B and v.bit_count()==exact
                logical_cases+=1
            F=gcd(gcd(a,b),(1<<N)|1)
            if N%2==0 and F==5:
                repeated_case=True
            recipes+=1
    assert orientation_detected and repeated_case
    return dict(status='passed',recipes=recipes,pinned_enumerator_cases=pin_cases,
                nontrivial_witness_cases=logical_cases,
                controls=['R=0 parallel loops','F=1 no logical distance','even N repeated F','wrong pin orientation detected'],
                evidence='independent finite matrix enumeration; not a proof premise; code added after symbolic reviews')

if __name__=='__main__':
    result=validate()
    Path(__file__).with_name('verification.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result))
