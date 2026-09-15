from pathlib import Path
import json,hashlib,sys
H=Path(__file__).resolve().parent;A=H/'experiment';sys.path.insert(0,str(H.parents[4]))
from pipelines.quantum_formalize.dag_view import render
r=json.loads((A/'result.json').read_text());assert all(r[k] for k in ['experiment_passed','assembly_accepted','environment_unchanged'])
s=json.loads((A/'nodes/state.json').read_text());assert len(s['nodes'])==7 and all(n['accepted'] for n in s['nodes'].values())
(H/'ATTEMPTS.json').write_text(json.dumps({k:len(v['result']['attempts'])for k,v in s['nodes'].items()},indent=2)+'\n')
(H/'GRAPH.md').write_text(render(H/'graph.json',A/'nodes/state.json'))
(H/'RESULTS.md').write_text('''# Actual arithmetic residual recovery accepted

The seven frozen targets connect the actual M5/source-orbit arithmetic residual to the finite set of uncovered residue completions. They prove exact cardinality and nonnegativity, disjoint-child arithmetic partition, and zero-root equivalence with coverage. Positive root count yields one full-length trace endpoint with positive count, an actual completed leaf outside all prior orbits, a fresh normalized canonical representative preserving GoodBases, and strict decrease of both the remaining cardinality and actual root-count natural measure.

Production path is computed once by DescentTrace.trace, and word is its endpoint; no second recover computation appears. The path check theorem gives its exact 2m replay calls. The parent generator separately uses cached root values to prove its production-call budget; optional full path transcripts do not belong to its baseline compact output-space bound.

GoodBases is precisely actual class validity for each stored representative and accepted canonical normalization. No free residual-count oracle, assumed complete family, stronger canonical-signature membership condition or new well-founded obligation is introduced. This is the original finite-fuel correctness interface, not the final generator theorem.

The two pending parent closures were promoted only after complete canonical receipt/source/target/payload verification. A preparer initially rejected the parents' same-name GraphPreflight.lean check file; the retained log records this harmless name collision. The fix skips that unimported parent check file and retains this module's original exact targets. All target definitions remained unchanged. Normal final proof, assembly, unchanged-environment and independent exact-type/axiom checks passed.
''')
m={str(p.relative_to(H)):hashlib.sha256(p.read_bytes()).hexdigest()for p in H.rglob('*')if p.is_file()and p!=H/'MANIFEST.json'and'__pycache__'not in p.parts};(H/'MANIFEST.json').write_text(json.dumps({'file_count':len(m),'files':m},indent=2)+'\n');print('finished',len(m))
