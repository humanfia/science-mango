#!/usr/bin/env python3
"""M7 orbit-coverage prototype and independent finite falsifier checks."""
from functools import lru_cache
from itertools import combinations, product
from math import gcd
from pathlib import Path
import json
import oracle_m5 as m5
import distance_m6 as m6

def signature(N,pair):
    a,b=pair
    return m5.pgcd(m5.pgcd(m5.poly(a),m5.poly(b)),(1<<N)|1)

def anchored_orbit(N,pair):
    out=set()
    for unit in range(N):
        if gcd(unit,N)!=1:continue
        a,b=[tuple((unit*x)%N for x in block) for block in pair]
        for anchor_a in a:
            aa=tuple(sorted((x-anchor_a)%N for x in a))
            for anchor_b in b:
                bb=tuple(sorted((x-anchor_b)%N for x in b))
                out.add((aa,bb));out.add((bb,aa))
    return out

def prefix_matches(pair,A,B,WA,WB):
    return all(set(chosen)<=set(block)<=set(chosen)|set(available)
               for block,chosen,available in zip(pair,(A,B),(WA,WB)))

def generate(N,w,sectors=None):
    if not 1<=w<=N:
        return [],dict(classes=0,constructed_pairs=0,covered_pairs=0,sector_counts={})
    sectors=tuple(m5.divisors((1<<N)|1) if sectors is None else sorted(set(sectors)))
    seen=set();covered=set();emitted=[];root_counts={}
    for F in sectors:
        if F<1 or m5.rem((1<<N)|1,F):
            raise ValueError('signature must divide cyclic modulus')
        root=m5.completion(N,w,F)
        root_counts[F]=root
        while True:
            covered_F={p for p in covered if signature(N,p)==F}
            def residual(A=(0,),B=(0,),WA=tuple(range(1,N)),WB=tuple(range(1,N))):
                full=m5.completion(N,w,F,A,B,WA,WB)
                known=sum(prefix_matches(p,A,B,WA,WB) for p in covered_F)
                answer=full-known
                assert answer>=0
                return answer
            if residual()==0:break
            A=(0,);B=(0,);WA=tuple(range(1,N));WB=WA
            for block in range(2):
                for position in range(1,N):
                    if block==0:
                        WA=WA[1:]
                        if residual(A,B,WA,WB)==0:A+=(position,)
                    else:
                        WB=WB[1:]
                        if residual(A,B,WA,WB)==0:B+=(position,)
                    assert residual(A,B,WA,WB)>0
            pair=(A,B);orbit=anchored_orbit(N,pair);canonical=min(orbit)
            assert signature(N,pair)==F and len(A)==len(B)==w
            assert gcd(N,*A,*B)==1 and pair not in covered and canonical not in seen
            seen.add(canonical);covered.update(orbit)
            emitted.append(dict(canonical=canonical,sector_witness=pair,F=F))
        assert sum(signature(N,p)==F for p in covered)==root
    return emitted,dict(classes=len(seen),constructed_pairs=len(emitted),covered_pairs=len(covered),sector_counts=root_counts)

@lru_cache(None)
def exact_label(N,pair):
    a,b=map(m5.poly,pair)
    result=m6.distance_witness(N,a,b)
    return 2*(signature(N,pair).bit_length()-1),result['distance']

def placements(N,pair):
    # Maps each realizable locality point to one replayable placement.
    points={}
    for unit in range(N):
        if gcd(unit,N)!=1:continue
        for s in range(N):
            for t in range(N):
                coords=[(unit*x+s)%N for x in pair[0]]+[(unit*x+t)%N for x in pair[1]]
                costs=[min(x,N-x) for x in coords]
                points.setdefault((sum(costs),max(costs)),(unit,s,t))
    return points

def nondominated(points):
    return {p for p in points if not any(q!=p and all(x<=y for x,y in zip(q,p)) for q in points)}

def select(N,w,allowed_k=None,d_floor=None,maximize_distance=False,sectors=None):
    emitted,certificate=generate(N,w,sectors)
    options={}
    for entry in emitted:
        pair=entry['canonical'];k,d=exact_label(N,pair)
        if allowed_k is not None and k not in allowed_k:continue
        if (d_floor is not None and (d is None or d<d_floor)) or (maximize_distance and d is None):continue
        local=placements(N,pair)
        options[pair]={((-d,)+p if maximize_distance else p):witness for p,witness in local.items()}
    front=nondominated(set().union(*(set(points) for points in options.values())) if options else set())
    winners={pair:{point:witness for point,witness in points.items() if point in front}
             for pair,points in options.items() if set(points)&front}
    return winners,front,certificate

# Independent reference traverses the raw domain only for finite validation.
def raw_orbit(N,pair):
    return {(tuple(sorted((unit*x+s)%N for x in left)),tuple(sorted((unit*x+t)%N for x in right)))
            for unit in range(N) if gcd(unit,N)==1
            for left,right in (pair,pair[::-1])
            for s in range(N) for t in range(N)}

def brute_classes(N,w,sectors=None):
    blocks=list(combinations(range(N),w));covered=set();result=set()
    for a,b in product(blocks,repeat=2):
        pair=(a,b)
        if pair in covered:continue
        # Connectivity uses support differences before anchoring.
        if gcd(N,*[x-a[0] for x in a],*[x-b[0] for x in b])!=1:continue
        orbit=raw_orbit(N,pair);covered.update(orbit)
        if sectors is not None and not any(signature(N,q) in sectors for q in orbit):continue
        result.add(min(orbit))
    return result

def brute_label(N,pair):
    B,C=m6.matrix_sets(N,*map(m5.poly,pair))
    k=(len(C)//len(B)).bit_length()-1
    d=min((v.bit_count() for v in C-B),default=None)
    return k,d

def brute_select(N,w,allowed_k=None,d_floor=None,maximize_distance=False):
    options={}
    for pair in brute_classes(N,w):
        k,d=brute_label(N,pair)
        if allowed_k is not None and k not in allowed_k:continue
        if (d_floor is not None and (d is None or d<d_floor)) or (maximize_distance and d is None):continue
        pts=set()
        for a,b in raw_orbit(N,pair):
            costs=[min(x,N-x) for x in a+b]
            point=(sum(costs),max(costs));pts.add((-d,)+point if maximize_distance else point)
        options[pair]=pts
    front=nondominated(set().union(*options.values()) if options else set())
    return {pair:points&front for pair,points in options.items() if points&front},front

def validate():
    generation=queries=0;strict_reduction=False;signature_transport=False;tied=False;empty=False
    for N in range(1,7):
        for w in range(1,N+1):
            emitted,cert=generate(N,w);expected=brute_classes(N,w)
            assert {e['canonical'] for e in emitted}==expected
            assert cert['constructed_pairs']==len(expected)
            strict_reduction|=cert['covered_pairs']>cert['constructed_pairs']
            generation+=1
    # Full-signature sectors move under common-unit equivalence at N=7.
    N=7
    for F in m5.divisors((1<<N)|1):
        emitted,_=generate(N,3,(F,))
        assert {e['canonical'] for e in emitted}==brute_classes(N,3,(F,))
        signature_transport|=any(signature(N,e['canonical'])!=F for e in emitted)
        generation+=1
    for N in range(1,6):
        for w in range(1,N+1):
            for settings in ({},{'d_floor':2},{'maximize_distance':True},{'allowed_k':{2}},{'allowed_k':{2*N+2}}):
                winners,front,_=select(N,w,**settings);bw,bf=brute_select(N,w,**settings)
                assert {p:set(points) for p,points in winners.items()}==bw and front==bf,(N,w,settings)
                for pair,points in winners.items():
                    for point,(unit,s,t) in points.items():
                        coords=[(unit*x+s)%N for x in pair[0]]+[(unit*x+t)%N for x in pair[1]]
                        costs=[min(x,N-x) for x in coords]
                        assert point[-2:]==(sum(costs),max(costs))
                tied|=len(winners)>1;empty|=not winners;queries+=1
    assert strict_reduction and signature_transport and empty
    return dict(status='passed',generation_cases=generation,optimization_queries=queries,
                signature_transport_detected=signature_transport,strict_leaf_reduction_detected=strict_reduction,
                tied_optima_observed=tied,empty_queries_observed=empty,
                evidence='finite prototype validation; not a uniform proof or prior-review premise')

if __name__=='__main__':
    result=validate()
    Path(__file__).with_name('verification.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result))
