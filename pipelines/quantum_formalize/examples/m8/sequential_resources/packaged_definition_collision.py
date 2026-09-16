import hashlib,json,re
from pathlib import Path

def reconcile_packaged_definition(left,right,repo):
    if left.name.endswith('Accepted.lean'):
        return None
    audit=repo/'pipelines/quantum_formalize/examples/m6/final/DEFINITION_PACKAGING.json'
    rows=json.loads(audit.read_text())['modules']
    row=next((r for r in rows if r['module']==left.stem),None)
    if row is None:return None
    sha=lambda data:hashlib.sha256(data).hexdigest()
    a,b=left.read_bytes(),right.read_bytes()
    if {sha(a),sha(b)}!={row['source_sha256'],row['packaged_sha256']}:return None
    body=lambda data:re.sub(r'^import [^\n]+\n','',data.decode(),flags=re.M)
    assert body(a)==body(b) and sha(body(a).encode())==row['body_sha256']
    chosen=a if sha(a)==row['packaged_sha256'] else b
    return chosen,{'module':left.name,'kept_sha256':sha(chosen),'left_sha256':sha(a),'right_sha256':sha(b),'body_sha256':row['body_sha256'],'packaging_audit':str(audit),'packaging_audit_sha256':sha(audit.read_bytes()),'rule':'Exact registered M6 final source/packaged hashes and byte-identical body; choose already verified minimal definition imports; full child closure rebuild required'}
