from pathlib import Path
import json,hashlib,sys
H=Path(__file__).resolve().parent;A=H/'experiment';sys.path.insert(0,str(H.parents[4]))
from pipelines.quantum_formalize.dag_view import render
r=json.loads((A/'result.json').read_text());assert all(r[k] for k in ['experiment_passed','assembly_accepted','environment_unchanged'])
s=json.loads((A/'nodes/state.json').read_text());assert len(s['nodes'])==5 and all(n['accepted'] for n in s['nodes'].values())
(H/'ATTEMPTS.json').write_text(json.dumps({k:len(v['result']['attempts'])for k,v in s['nodes'].items()},indent=2)+'\n')
(H/'GRAPH.md').write_text(render(H/'graph.json',A/'nodes/state.json'))
(H/'RESULTS.md').write_text('''# Concrete complete query sectors accepted

The five frozen targets prove that the explicit finite multiset-factor enumeration is exactly all monic divisors of the actual cyclic modulus. Factor multiplicities are preserved: the multiset powerset is taken before duplicate removal. This includes even moduli with repeated irreducible factors.

The effective query sectors retain a supplied some E unchanged and replace none by that complete finite set. Query validity implies the exact arithmetic PrefixSector.ValidSector condition. For every actual recipe, full-signature membership is equivalent to DefaultQuery.allows, without an added query-validity assumption. Thus no free sector-set oracle remains in this interface.

All targets passed normal frozen compilation, independent exact-type/axiom checks, full assembly and unchanged-environment checks. Parent receipts, original drafts, rendered candidate hashes and portable declarations were verified before import. The experiment uses two workers and 600-second compiler limits; complete attempt evidence is retained.
''')
m={str(p.relative_to(H)):hashlib.sha256(p.read_bytes()).hexdigest()for p in H.rglob('*')if p.is_file()and p!=H/'MANIFEST.json'and'__pycache__'not in p.parts};(H/'MANIFEST.json').write_text(json.dumps({'file_count':len(m),'files':m},indent=2)+'\n');print('finished',len(m))
