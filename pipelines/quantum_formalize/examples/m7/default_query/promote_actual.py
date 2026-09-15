from pathlib import Path
import json,hashlib,sys,shutil
H=Path(__file__).resolve().parent; repo=H.parents[4];sys.path.insert(0,str(repo))
from pipelines.quantum_formalize.engine import Spec,render,digest
from pipelines.quantum_formalize.dag_runner import load_graph,portable_declaration
A=H.parent/'actual_presentation/experiment'; P=Path('/home/jing/m7-lean-default-query-formalization')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
m=json.loads((A/'MANIFEST.json').read_text());assert m['file_count']==len(m['files'])
for n,h in m['files'].items():assert sha(A/n)==h
r=json.loads((A/'result.json').read_text());assert r['experiment_passed'] and r['assembly_accepted'] and r['environment_unchanged']
g,nodes=load_graph(A/'graph.json');state=json.loads((A/'nodes/state.json').read_text());decs=[];provenance={}
for n in nodes:
 rec=state['nodes'][n.id];assert rec['accepted'] and rec==json.loads((A/'nodes'/n.id/'receipt.json').read_text())
 r=rec['result'];last=r['attempts'][-1];folder=A/'node_runs'/n.id/Path(last['proof_path']).parent.name
 spec=Spec.model_validate(json.loads((A/'nodes'/n.id/'resolved-spec.json').read_text()));assert spec.statement==n.spec['statement']
 draft=json.loads((folder/'draft.json').read_text());cand=folder/Path(last['proof_path']).name;target=folder/Path(last['target_path']).name
 assert sha(cand)==last['source_sha256'] and sha(target)==last['target_sha256']
 assert cand.read_text()==render(spec,draft['proof'],target.stem)
 art=r['artifacts'][n.id];assert digest(art['payload'])==art['sha256'];assert digest(n.spec)==art['payload']['spec_sha256']
 dec=portable_declaration(spec,draft['proof']);assert dec==art['payload']['declaration'];decs.append(dec)
 provenance[n.id]={'payload_sha256':art['sha256'],'source_sha256':last['source_sha256'],'target_sha256':last['target_sha256']}
text='import M7ActualPresentation\nimport M7PresentationAccepted\n\n'+'\n\n'.join(decs)+'\n';(P/'M7ActualPresentationAccepted.lean').write_text(text);(H/'lean/M7ActualPresentationAccepted.lean').write_text(text)
assert (P/'M7ActualPresentation.lean').read_bytes()==(H.parent/'actual_presentation/lean/M7ActualPresentation.lean').read_bytes()
shutil.copy2(P/'M7ActualPresentation.lean',H/'lean/M7ActualPresentation.lean')
(H/'PROMOTION.json').write_text(json.dumps({'canonical_manifest_sha256':sha(A/'MANIFEST.json'),'verified_count':len(decs),'verified_receipt_payload_source_and_frozen_type':True,'source_definition_sha256':sha(P/'M7ActualPresentation.lean'),'module_sha256':sha(P/'M7ActualPresentationAccepted.lean'),'nodes':provenance},indent=2)+'\n')
print('Verified and promoted',len(decs),'unchanged accepted declarations')
