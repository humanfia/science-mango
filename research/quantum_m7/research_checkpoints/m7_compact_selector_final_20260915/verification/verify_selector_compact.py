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

def canonical_compact(N,pair):
    candidates=[]
    for unit in range(N):
        if gcd(unit,N)!=1:continue
        blocks=[]
        for support in pair:
            scaled=tuple((unit*x)%N for x in support)
            blocks.append(min(tuple(sorted((x-anchor)%N for x in scaled)) for anchor in scaled))
        candidates.append(tuple(sorted(blocks)))
    return min(candidates)

@lru_cache(None)
def group_numerator(N,pair,F,A,B,WA,WB):
    total=0
    for unit in range(N):
        if gcd(unit,N)!=1:continue
        scaled=tuple(tuple((unit*x)%N for x in block) for block in pair)
        if F is not None and signature(N,scaled)!=F:continue
        # Each block is counted independently; products are integer products,
        # never Cartesian products of translated support pairs.
        for left,right in (scaled,scaled[::-1]):
            ways=[]
            for support,chosen,available in zip((left,right),(A,B),(WA,WB)):
                allowed=set(chosen)|set(available);required=set(chosen)
                count=0
                for shift in range(N):
                    transformed={(x+shift)%N for x in support}
                    count+=required<=transformed<=allowed
                ways.append(count)
            total+=ways[0]*ways[1]
    return total

@lru_cache(None)
def stabilizer(N,pair):
    value=group_numerator(N,pair,None,pair[0],pair[1],(),())
    assert value>0
    return value

def orbit_count(N,pair,F,A=(0,),B=(0,),WA=None,WB=None):
    if WA is None:WA=tuple(range(1,N))
    if WB is None:WB=tuple(range(1,N))
    num=group_numerator(N,pair,F,A,B,WA,WB);den=stabilizer(N,pair)
    assert num%den==0
    return num//den

def generate(N,w,sectors=None):
    if not 1<=w<=N:
        return [],dict(classes=0,constructed_pairs=0,covered_pairs=0,sector_counts={},explicit_orbit_members=0)
    sectors=tuple(m5.divisors((1<<N)|1) if sectors is None else sorted(set(sectors)))
    representatives=[];emitted=[];root_counts={}
    for F in sectors:
        if F<1 or m5.rem((1<<N)|1,F):raise ValueError('invalid signature')
        root_counts[F]=m5.completion(N,w,F)
        def residual(A=(0,),B=(0,),WA=tuple(range(1,N)),WB=tuple(range(1,N))):
            count=m5.completion(N,w,F,A,B,WA,WB)-sum(orbit_count(N,p,F,A,B,WA,WB) for p in representatives)
            assert count>=0
            return count
        while residual()>0:
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
            pair=(A,B);canonical=canonical_compact(N,pair)
            assert canonical not in representatives and signature(N,pair)==F
            representatives.append(canonical)
            emitted.append(dict(canonical=canonical,sector_witness=pair,F=F))
    covered=sum(orbit_count(N,p,None) for p in representatives)
    return emitted,dict(classes=len(representatives),constructed_pairs=len(emitted),covered_pairs=covered,sector_counts=root_counts,explicit_orbit_members=0)

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
    Path(__file__).with_name('verification-compact.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result))
