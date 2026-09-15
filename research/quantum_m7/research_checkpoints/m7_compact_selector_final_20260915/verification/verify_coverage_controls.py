"""Finite coverage-certificate corruption checks for the compact prototype."""
import json
from pathlib import Path
import verify_selector_compact as s


def verify(N,w,entries,certificate,sectors=None):
    sectors=tuple(s.m5.divisors((1<<N)|1) if sectors is None else sectors)
    reps=[]
    for e in entries:
        pair=e['canonical']; witness=e['sector_witness']
        assert pair==s.canonical_compact(N,pair) and pair not in reps
        assert all(len(block)==w and len(set(block))==w and 0 in block and all(0<=x<N for x in block) for block in pair)
        assert s.gcd(N,*pair[0],*pair[1])==1
        assert e['F'] in sectors and s.signature(N,witness)==e['F']
        assert s.orbit_count(N,pair,None,witness[0],witness[1],(),())==1
        reps.append(pair)
    for F in sectors:
        root=s.m5.completion(N,w,F)
        assert certificate['sector_counts'][F]==root
        assert sum(s.orbit_count(N,pair,F) for pair in reps)==root
    assert certificate['classes']==certificate['constructed_pairs']==len(reps)
    assert certificate['explicit_orbit_members']==0


def validate():
    entries,cert=s.generate(7,3); verify(7,3,entries,cert)
    controls=[]
    bad_count=dict(cert,sector_counts={**cert['sector_counts'],1:cert['sector_counts'][1]+1})
    for name,es,cs in [('missing_class',entries[:-1],cert),('duplicate_class',entries+[entries[0]],cert),('wrong_root_count',entries,bad_count)]:
        try: verify(7,3,es,cs)
        except AssertionError: controls.append(name)
        else: raise AssertionError(name)
    def forbidden(*args): raise AssertionError('raw reference called by production generator')
    old_orbit,old_classes=s.raw_orbit,s.brute_classes
    try:
        s.raw_orbit=s.brute_classes=forbidden
        again,c2=s.generate(7,3); verify(7,3,again,c2)
        assert again==entries
    finally:
        s.raw_orbit,s.brute_classes=old_orbit,old_classes
    return {'status':'passed','replayed_classes':len(entries),'corruptions_rejected':controls,'raw_reference_functions_disabled_during_generation':True,'scope':'additional finite compact-coverage certificate checks; not a proof premise'}


if __name__=='__main__':
    result=validate()
    Path(__file__).with_name('coverage-controls.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result))
