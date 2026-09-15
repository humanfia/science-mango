from pathlib import Path
import json,hashlib,sys
H=Path(__file__).resolve().parent;sys.path.insert(0,str(H.parents[4]));P=Path('/home/jing/m7-lean-query-rebase-formalization')
from pipelines.quantum_formalize.engine import Spec,render,digest
from pipelines.quantum_formalize.dag_runner import load_graph,portable_declaration
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();allp={}
for stage,module,header,definition,count in [('action','M7ActionAccepted','import M7Action\n','M7Action',13),('global_query','M7GlobalQueryAccepted','import M7GlobalQuery\nimport M7SelectionAccepted\nimport M7ActualPresentationAccepted\n','M7GlobalQuery',9)]:
 A=H.parent/stage/'experiment';m=json.loads((A/'MANIFEST.json').read_text());files=m.get('files',m)
 for n,h in files.items():assert sha(A/n)==h
 r=json.loads((A/'result.json').read_text());assert r['experiment_passed'] and r['assembly_accepted'] and r['environment_unchanged']
 g,nodes=load_graph(A/'graph.json');assert len(nodes)==count;s=json.loads((A/'nodes/state.json').read_text());decs=[];proofs={}
 for n in nodes:
  rec=s['nodes'][n.id];assert rec['accepted'] and rec==json.loads((A/'nodes'/n.id/'receipt.json').read_text());r=rec['result'];last=r['attempts'][-1];folder=A/'node_runs'/n.id/Path(last['proof_path']).parent.name;spec=Spec.model_validate(json.loads((A/'nodes'/n.id/'resolved-spec.json').read_text()));assert spec.statement==n.spec['statement'];draft=json.loads((folder/'draft.json').read_text());cand=folder/Path(last['proof_path']).name;target=folder/Path(last['target_path']).name
  assert sha(cand)==last['source_sha256'] and sha(target)==last['target_sha256'];assert cand.read_text()==render(spec,draft['proof'],target.stem);art=r['artifacts'][n.id];assert digest(art['payload'])==art['sha256'];assert digest(n.spec)==art['payload']['spec_sha256'];dec=portable_declaration(spec,draft['proof']);assert dec==art['payload']['declaration'];decs.append(dec);proofs[n.id]={'payload_sha256':art['sha256'],'source_sha256':last['source_sha256'],'target_sha256':last['target_sha256']}
 assert (P/(definition+'.lean')).read_bytes()==(H.parent/stage/'lean'/(definition+'.lean')).read_bytes();text=header+'\n'+'\n\n'.join(decs)+'\n'
 for d in [P,H/'lean']:(d/(module+'.lean')).write_text(text)
 allp[stage]={'verified_count':count,'canonical_manifest_sha256':sha(A/'MANIFEST.json'),'module_sha256':sha(P/(module+'.lean')),'definition_sha256':sha(P/(definition+'.lean')),'nodes':proofs}
(H/'PROMOTION.json').write_text(json.dumps({'verified_receipt_payload_source_and_frozen_type':True,'stages':allp},indent=2)+'\n');print('Verified/promoted',sum(x['verified_count']for x in allp.values()))
