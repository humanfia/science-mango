from pathlib import Path
import json
sections={
'ActionSignature':{'action':['record_card','order_one_records'],'actual_signature':['signature_properties','action_signature','tau_degree','source_orbit_quotient'],'actual_factorized':['stabilizer_numerator','positive_denominator','exact_orbit_quotient'],'prefix_orbit':['residual_card','residual_positive']},
'Canonical':{'canonical_outer':['canonical_minimal','realizer_correct','realizer_inverse','canonical_invariant','orbit_complete'],'canonical_classes':['idempotent']},
'Generation':{'compact_correctness':['run_records','generate_exact','generate_card','generate_coverage'],'generated_family':'all','overfull_boundary':'all','query_sectors':'all'},
'Selector':{'global_query':['winning_classes'],'final_selector':'all','default_query':['sector_modes','noLogical_policy','empty_objectives'],'actual_presentation':['four_field_order','leastAction_spec','presentation_exact']},
'PhysicalLabels':{'generated_labels':'all'},
'Replay':{'final_replay':'all','generation_replay':['generate_checked','checked_coverage'],'label_replay':['trace_recover','check_sound','self_check','checked_physical_answer'],'factor_replay':'all'},
'Resources':{'final_resources':'all','scalar_work':['prefix_bound','sector_bound','mask_positions'],'compact_storage':['emission_valid','encode_core','unit_table_recovery','storage_bounds'],'generation_calls':['generate_count'],'streaming_cost':['stream_projection_bound','scan_bound','record_cardinality'],'objective_comparison':['compare_exact','compare_bound']},
'PresentationExtensions':{'selection':['selector_exact','selector_strict_dominator','empty_objectives'],'actual_presentation':['winning_fiber','presentation_sound']}}
aliases={'global_query':'M7GlobalQueryAccepted','action':'M7ActionAccepted','actual_signature':'M7RecipeSignatureAccepted','actual_factorized':'M7ActualFactorizedAccepted','prefix_orbit':'M7PrefixOrbitAccepted','canonical_outer':'M7CanonicalOuterAccepted','canonical_classes':'M7CanonicalClassesAccepted','compact_correctness':'M7CompactCorrectnessAccepted','generated_family':'M7GeneratedFamilyAccepted','overfull_boundary':'M7OverfullBoundaryAccepted','query_sectors':'M7QuerySectorsAccepted','final_selector':'M7FinalSelectorAccepted','default_query':'M7DefaultQueryAccepted','actual_presentation':'M7ActualPresentationAccepted','generated_labels':'M7GeneratedLabelsAccepted','final_replay':'M7FinalReplayAccepted','generation_replay':'M7GenerationReplayAccepted','label_replay':'M7LabelReplayAccepted','factor_replay':'M7FactorReplayAccepted','final_resources':'M7FinalResourcesAccepted','scalar_work':'M7ScalarWorkAccepted','compact_storage':'M7CompactStorageAccepted','generation_calls':'M7GenerationCallsAccepted','streaming_cost':'M7StreamingCostAccepted','objective_comparison':'M7ObjectiveComparisonAccepted','selection':'M7SelectionAccepted'}
s=Path('/home/jing/m7_prepare_prefix_orbit.py').read_text();head=s.split("source='''",1)[0]
head=head.replace("b=base/'prefix_orbit'","b=base/'final'").replace('m7-lean-prefix-orbit-formalization','m7-lean-final-formalization')
head=head.replace("parents=[('residue_prefix','M7ResiduePrefixAccepted'),('actual_signature','M7RecipeSignatureAccepted'),('connectivity','M7ConnectivityAccepted'),('canonical_classes','M7CanonicalClassesAccepted'),('orbit_residual','M7OrbitResidualAccepted')]",'parents='+repr(list(aliases.items())))
exec(head)
source=''.join('import '+v+'\n' for v in aliases.values())+'\nnamespace M7.Final\n'
claim_map={};proof_names={}
for section,batches in sections.items():
 clauses=[];refs=[];claim_map[section]=[]
 for batch,selected in batches.items():
  graph=json.loads((base/batch/'experiment/graph.json').read_text());nodes={n['id']:n for n in graph['nodes']}
  chosen=list(nodes) if selected=='all' else selected
  for node_id in chosen:
   n=nodes[node_id];spec=n['spec'];assert not spec.get('context','').strip(),(batch,node_id,'nonempty context')
   clauses.append('('+spec['statement']+')');refs.append(spec['name']);claim_map[section].append({'batch':batch,'target':spec['name'],'receipt':str((base/batch/'experiment/result.json').relative_to(repo)),'statement':spec['statement']})
 source+='\n/-- Exact frozen original-scope clauses; no correctness proposition is an input. -/\nnoncomputable def '+section+' : Prop :=\n  '+' ∧\n  '.join(clauses)+'\n'
 proof_names[section]=refs
source+='\nnoncomputable def OriginalM7 : Prop :=\n  '+' ∧ '.join(sections)+'\nend M7.Final\n'
(p/'M7Final.lean').write_text(source);(b/'lean/M7Final.lean').write_text(source)
src=base/'final_replay'
for n in ['lake-manifest.json','lean-toolchain']:shutil.copy2(src/n,p/n);shutil.copy2(src/n,b/n)
s=(src/'lakefile.toml').read_text();s=re.sub(r'^name = ".*?"','name = "M7Final"',s,count=1,flags=re.M);s=re.sub(r'^defaultTargets = .*','defaultTargets = ["M7Final"]',s,flags=re.M)
for f0 in sorted(p.glob('*.lean')):
 if f0.stem!='Preflight' and ('[[lean_lib]]\nname = "'+f0.stem+'"')not in s:s+='\n[[lean_lib]]\nname = "'+f0.stem+'"\n'
(p/'lakefile.toml').write_text(s);shutil.copy2(p/'lakefile.toml',b/'lakefile.toml');(p/'.lake').mkdir(exist_ok=True)
if not(p/'.lake/packages').exists():(p/'.lake/packages').symlink_to('/home/jing/lean-1st-proof/.lake/packages',target_is_directory=True)
nodes=[]
for section in sections:
 guide='Original M7 final composition, exact canonical clauses. Unfold M7.Final.'+section+' then construct the nested conjunction using exactly these accepted theorem references in order: '+', '.join(proof_names[section])+'. No new hypothesis, assumed oracle, target edits, axiom, or sorry. Preserve the source arithmetic/exact-reduction scope, no M8/runtime/extraction strengthening. Return tactic lines only.'
 nodes.append({'id':section.lower(),'dependencies':[],'spec':{'name':'M7.Final.'+section.lower(),'statement':'M7.Final.'+section,'imports':['M7Final'],'context':'','queries':['algebra'],'guidance':guide}})
nodes.append({'id':'original_m7','dependencies':[s.lower() for s in sections],'spec':{'name':'M7.Final.original_m7','statement':'M7.Final.OriginalM7','imports':['M7Final'],'context':'','queries':['algebra'],'guidance':'Compose the eight accepted section theorems, in the order of the OriginalM7 definition. This is the complete frozen original M7 mathematical algorithm/replay/resource contract. Do not add assumptions or substitute a component count for the root. Return tactic lines only.'}})
graph={'title':'Original complete M7 closed formal acceptance root','nodes':nodes};(b/'graph.json').write_text(json.dumps(graph,indent=2)+'\n');(p/'Preflight.lean').write_text('import M7Final\n'+''.join('def target_'+str(j)+' : Prop := '+n['spec']['statement']+'\n'for j,n in enumerate(nodes)));(b/'IMPORT_PROVENANCE.json').write_text(json.dumps(prov,indent=2)+'\n');(b/'CLAIM_MAP.json').write_text(json.dumps(claim_map,indent=2)+'\n')
ctl=Path('/home/jing/m7_canonical_preflight_launch.py').read_text().replace('canonical-block','final').replace('canonical_block','final').replace('M7CanonicalBlock','M7Final').replace('13 exact','9 exact').replace("env['M7_COMPILE_TIMEOUT']='600'","env['M7_COMPILE_TIMEOUT']='600';env['M7_BROAD_RETRIEVAL']='1'")
cp=Path('/home/jing/m7_final_preflight_launch.py');cp.write_text(ctl);shutil.copy2(cp,b/'preflight_launch.py');shutil.copy2('/home/jing/m7_launch_batch.py',b/'launch_batch.py');log=(b/'controller.log').open('a');proc=subprocess.Popen(['/home/jing/quantum_code_discovery_proof/.venv-harness/bin/python',str(cp)],cwd=repo,stdout=log,stderr=subprocess.STDOUT,start_new_session=True);print({'prepared':len(nodes),'clauses':sum(map(len,claim_map.values())),'controller_pid':proc.pid})
