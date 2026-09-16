from pathlib import Path
import hashlib,json,re
from pipelines.quantum_formalize.accepted_order import _parts

def forward_m6_accepted(project,stage):
    aggregate=project/'M6FinalDependencies.lean'
    allparts=_parts(aggregate.read_text());assert allparts
    alld=allparts[1];rows=[];originals=stage/'forwarded_sources';originals.mkdir(exist_ok=True)
    sha=lambda s:hashlib.sha256(s.encode()).hexdigest()
    for f in sorted(project.glob('M6*Accepted.lean')):
        original=f.read_text();parts=_parts(original)
        if parts is None:continue
        declarations=parts[1];overlap=set(declarations)&set(alld)
        if not overlap:continue
        assert overlap==set(declarations),(f.name,'partial overlap')
        assert all(alld[n]==v for n,v in declarations.items()),(f.name,'declaration mismatch')
        (originals/f.name).write_text(original)
        forwarded='import M6FinalReady\n'
        f.write_text(forwarded);(stage/'lean'/f.name).write_text(forwarded)
        rows.append({'module':f.name,'original_sha256':sha(original),'forwarded_sha256':sha(forwarded),'declaration_sha256':{n:sha(v) for n,v in declarations.items()},'aggregate':'M6FinalDependencies.lean','aggregate_sha256':sha(aggregate.read_text()),'rule':'All exact named theorem statements and complete proof bodies already present byte-for-byte in canonical aggregate; import-only forwarding; original source retained; full child build required'})
    edges={f.stem:[i for line in re.findall(r'^import ([^\n]+)$',f.read_text(),re.M) for i in line.split()] for f in project.glob('*.lean')}
    active=set();done=set()
    def visit(n):
        if n not in edges or n in done:return
        assert n not in active,('import cycle',n)
        active.add(n)
        for d in edges[n]:visit(d)
        active.remove(n);done.add(n)
    for n in edges:visit(n)
    (stage/'ACCEPTED_FORWARDING.json').write_text(json.dumps({'modules':rows,'acyclic_import_graph':True},indent=2)+'\n')
    return rows

def reconcile_m6_forwarder(left,right,project):
    if not left.name.startswith('M6') or not left.name.endswith('Accepted.lean'):return None
    a,b=left.read_text(),right.read_text();shim='import M6FinalReady\n'
    if a!=shim and b!=shim:return None
    source=b if a==shim else a
    parts=_parts(source)
    if parts is None:return None
    aggregate=project/'M6FinalDependencies.lean'
    if not aggregate.exists():return None
    target=_parts(aggregate.read_text());assert target
    assert all(target[1].get(n)==v for n,v in parts[1].items()),('forwarding collision mismatch',left.name)
    sha=lambda s:hashlib.sha256(s.encode()).hexdigest()
    return shim.encode(),{'module':left.name,'left_sha256':sha(a),'right_sha256':sha(b),'forwarded_sha256':sha(shim),'aggregate_sha256':sha(aggregate.read_text()),'declarations':{n:sha(v) for n,v in parts[1].items()},'rule':'Exact canonical aggregate theorem bodies justify existing import-only forwarding; child must audit import DAG and rebuild'}
