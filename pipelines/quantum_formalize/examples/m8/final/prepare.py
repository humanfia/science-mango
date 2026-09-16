from pathlib import Path
import json,hashlib,shutil,subprocess,re,time,runpy,sys
repo=Path('/home/jing/science-mango-quantum-harness-publish-20260914');base=repo/'pipelines/quantum_formalize/examples/m8'
sys.path.insert(0,str(repo))
parents=[('solver','M8SolverAccepted'),('raw_parameters','M8RawParametersAccepted'),('sequential_resources','M8SequentialResourcesAccepted'),('sequential_store','M8SequentialStoreAccepted'),('whole_resources','M8WholeResourcesAccepted'),('coverage','M8CoverageAccepted'),('exclusion_conclusions','M8ExclusionConclusionsAccepted')]
for name,_ in parents:
 while not(base/name/'experiment/MANIFEST.json').exists():time.sleep(20)
helper=runpy.run_path(str(base/'import_normalization/css_superset.py'))
css_audit=helper['audit'](repo);shim='import M6FinalDependencies\n'
css_allowed={css_audit['wanted_source_sha256'],hashlib.sha256(shim.encode()).hexdigest()}
s=Path('/home/jing/m7_prepare_prefix_orbit.py').read_text().split("\nsource='''",1)[0]
s=s.replace("base=repo/'pipelines/quantum_formalize/examples/m7'","base=repo/'pipelines/quantum_formalize/examples/m8'").replace("b=base/'prefix_orbit'","b=base/'final'").replace('m7-lean-prefix-orbit-formalization','m8-lean-final-formalization')
s=re.sub(r"parents=\[.*\]",'parents='+repr(parents),s,count=1)
needle="  if (p/f.name).exists() and (p/f.name).read_bytes()!=f.read_bytes():"
assert needle in s
s=s.replace(needle,"""  if f.name == 'M6ActualCSSAccepted.lean':
   assert hashlib.sha256(f.read_bytes()).hexdigest() in css_allowed, ('unaudited CSS container',name)
   if (p/f.name).exists():assert hashlib.sha256((p/f.name).read_bytes()).hexdigest() in css_allowed
   (p/f.name).write_text(shim);(b/'lean'/f.name).write_text(shim)
   prov.append({'parent':name,'audited_css_superset_normalization':f.name,'incoming_sha256':env[f.name],'child_shim_sha256':hashlib.sha256(shim.encode()).hexdigest(),'rule':'All 105 imported theorem types and proof bodies and 13 definition files audited identical; no parent mutation; new child rebuilt'})
   continue
"""+needle)
packaging=runpy.run_path('/home/jing/m8_packaged_definition_collision.py')
forwarding=runpy.run_path('/home/jing/m8_forward_m6_accepted.py')
needle2="  if (p/f.name).exists() and (p/f.name).read_bytes()!=f.read_bytes():"
s=s.replace(needle2,needle2+"\n   reconciliation=packaging['reconcile_packaged_definition'](p/f.name,f,repo)\n   if reconciliation is None:reconciliation=forwarding['reconcile_m6_forwarder'](p/f.name,f,p)\n   if reconciliation is not None:\n    chosen,record=reconciliation;(p/f.name).write_bytes(chosen);(b/'lean'/f.name).write_bytes(chosen);prov.append({'parent':name,'audited_import_reconciliation':record});continue")
exec(s)
helper['normalize_child'](repo,p,b/'lean',b/'CSS_IMPORT_NORMALIZATION.json')
forwarding['forward_m6_accepted'](p,b)
selection=[('algorithm','Algorithm','solver',['output_gcd','noLogical_exact','unrecognized_exact','recognized_exact','recognized_correct']),('physical_parameters','PhysicalParameters','raw_parameters',['raw_noLogical','encoded_dimension']),('resources','Resources','sequential_resources',None),('storage','Storage','sequential_store',['allocation_access','store_space']),('cost_projection','CostProjection','whole_resources',['projection']),('coverage','AdmittedFamilies','coverage',None),('exclusion','ExcludedFamilies','exclusion_conclusions',None)]
source=''.join('import '+a+'\n' for _,a in parents)+'\nnamespace M8.Final\n'
rows=[];nodes=[]
for node,prop,stage,ids in selection:
 graph=json.loads((base/stage/'graph.json').read_text());chosen=[x for x in graph['nodes'] if ids is None or x['id'] in ids]
 assert chosen and (ids is None or {x['id'] for x in chosen}==set(ids))
 expressions=[];names=[]
 for x in chosen:
  spec=x['spec'];receipt=base/stage/'experiment/nodes'/x['id']/'resolved-spec.json';frozen=json.loads(receipt.read_text());assert frozen['statement']==spec['statement'] and frozen['name']==spec['name']
  expressions.append('('+spec['statement']+')');names.append(spec['name'])
  rows.append({'group':prop,'stage':stage,'id':x['id'],'name':spec['name'],'statement':spec['statement'],'statement_sha256':hashlib.sha256(spec['statement'].encode()).hexdigest(),'canonical_resolved_spec':str(receipt.relative_to(repo)),'resolved_spec_sha256':hashlib.sha256(receipt.read_bytes()).hexdigest()})
 source+='\n/-- Exact original-scope obligations copied from accepted frozen targets. -/\ndef '+prop+' : Prop :=\n  '+' ∧\n  '.join(expressions)+'\n'
 nodes.append({'id':node,'dependencies':[],'spec':{'name':'M8.Final.'+node,'statement':'M8.Final.'+prop,'imports':['M8Final'],'context':'','queries':['algebra'],'guidance':'Unfold only M8.Final.'+prop+' and construct the conjunction using these exact accepted declarations, in order: '+', '.join(names)+'. No new hypotheses, no theorem axioms or changed scope. Return tactic lines only.'}})
props=[x[1] for x in selection]
source+='\n/-- Revised accepted original M8: exact algorithm, physical output, fixed sequential resources, and explicit admitted/excluded families. -/\ndef OriginalM8 : Prop :=\n  '+' ∧ '.join(props)+'\nend M8.Final\n'
nodes.append({'id':'original_m8','dependencies':[x[0] for x in selection],'spec':{'name':'M8.Final.original_m8','statement':'M8.Final.OriginalM8','imports':['M8Final'],'context':'','queries':['algebra'],'guidance':'Unfold M8.Final.OriginalM8 and assemble M8.Final.algorithm, physical_parameters, resources, coverage, exclusion in that order. This is the original root conjunction; no new goal or assumption. Return tactic lines only.'}})
(p/'M8Final.lean').write_text(source);(b/'lean/M8Final.lean').write_text(source)
(b/'ROOT_OBLIGATIONS.json').write_text(json.dumps({'status':'frozen root targets; root proof still pending','main_claim_sha256':json.loads((b/'PRIMARY_CLAIM.json').read_text())['claim_utf8_sha256'],'groups':props,'obligations':rows,'optional_refined_trialcount_required':False},indent=2)+'\n')
(b/'graph.json').write_text(json.dumps({'title':'Original accepted M8 root closure','nodes':nodes},indent=2)+'\n')
(b/'IMPORT_PROVENANCE.json').write_text(json.dumps(prov,indent=2)+'\n')
(p/'Preflight.lean').write_text('import M8Final\n'+''.join('def target_'+str(i)+' : Prop := '+n['spec']['statement']+'\n' for i,n in enumerate(nodes)))
src=base/'sequential_resources'
for n in ['lake-manifest.json','lean-toolchain']:shutil.copy2(src/n,p/n);shutil.copy2(src/n,b/n)
s=(src/'lakefile.toml').read_text();s=re.sub(r'^name = ".*?"','name = "M8Final"',s,count=1,flags=re.M);s=re.sub(r'^defaultTargets = .*','defaultTargets = ["M8Final"]',s,flags=re.M)
for f in sorted(p.glob('*.lean')):
 if f.stem!='Preflight' and ('[[lean_lib]]\nname = "'+f.stem+'"')not in s:s+='\n[[lean_lib]]\nname = "'+f.stem+'"\n'
(p/'lakefile.toml').write_text(s);shutil.copy2(p/'lakefile.toml',b/'lakefile.toml');(p/'.lake').mkdir(exist_ok=True)
if not(p/'.lake/packages').exists():(p/'.lake/packages').symlink_to('/home/jing/lean-1st-proof/.lake/packages',target_is_directory=True)
cache=runpy.run_path('/home/jing/m8_verified_cache.py')
cache_record=cache['reuse_verified_caches'](p,[Path('/home/jing/m8-lean-sequential-resources-formalization')])
(b/'CACHE_REUSE.json').write_text(json.dumps(cache_record,indent=2)+'\n')
ctl=Path('/home/jing/m8_anchor_preflight_launch.py').read_text().replace('m8-lean-anchor','m8-lean-final').replace('examples/m8/anchor','examples/m8/final').replace('M8Anchor','M8Final').replace('8 exact','8 exact').replace("'anchor','anchor','2'","'final','final','2'")
cp=Path('/home/jing/m8_final_preflight_launch.py');cp.write_text(ctl)
for a,d in [(cp,b/'preflight_launch.py'),(Path('/home/jing/m8_prepare_final.py'),b/'prepare.py'),(Path('/home/jing/m8_launch_batch.py'),b/'launch_batch.py')]:shutil.copy2(a,d)
log=(b/'controller.log').open('a');q=subprocess.Popen(['/home/jing/quantum_code_discovery_proof/.venv-harness/bin/python',str(cp)],cwd=repo,stdout=log,stderr=subprocess.STDOUT,start_new_session=True);print({'targets':len(nodes),'controller_pid':q.pid},flush=True)
