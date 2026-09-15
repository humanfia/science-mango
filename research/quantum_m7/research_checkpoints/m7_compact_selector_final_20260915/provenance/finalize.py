"""Archive only a fully reviewed unchanged candidate after controller inspection."""
from pathlib import Path
import json,hashlib,shutil,datetime
repo=Path('/home/jing/quantum_code_discovery_proof')
run=repo/'.humanize-quantum-runs/run-a_w5g0fg'
area=repo/'.humanize-quantum-runs/m7-final-scope-20260915'
archive=repo/'research_checkpoints/m7_compact_selector_final_20260915'
c=json.loads((area/'candidate.json').read_text())
digest=hashlib.sha256(json.dumps(c,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode()).hexdigest()
assert digest=='44e9358d34dd671ce76b39cd5c1f64b6a16b5229b9d98ce0e21d813b557c7a99'
assert c['scope']=='selected_obligation' and not c['unproved_steps']
summary=json.loads((run/'summary.json').read_text())
assert summary['status']=='reviewed_candidate_pending_manual_integration',summary['status']
reviews=[]
for number,role in ((2,'reviewer_a'),(3,'reviewer_b')):
 call=run/f'call-{number:03d}'
 request=json.loads((call/'request.json').read_text()); assert request['role']==role
 review=json.loads((call/'response.json').read_text())
 assert review['candidate_sha256']==digest and review['verdict']=='no_gap_found' and not review['first_fault']
 assert all(review[key] for key in ('full_claim_checked','uniform_argument_checked','dependencies_checked','original_constraints_preserved','finite_tests_not_used_as_proof'))
 reviews.append(review)
 (archive/f'{role}.json').write_text(json.dumps(review,ensure_ascii=False,indent=2)+'\n')
 frozen=json.loads((call/'inputs/_snapshot.json').read_text())
 (archive/'provenance'/f'{role}-input-manifest.json').write_text(json.dumps(frozen,indent=2)+'\n')
 shutil.copy2(call/'activity.json',archive/'provenance'/f'{role}-activity.json')
# Every declared direct and structured transitive dependency is exact.
manifest=json.loads((archive/'dependency-manifest.json').read_text())
for ref in manifest['files']:
 data=(archive/'dependencies'/ref['path']).read_bytes()
 assert hashlib.sha256(data).hexdigest()==ref['sha256']
 assert data==(run/'snapshot'/ref['path']).read_bytes()
assert json.loads((run/'restart-audits.json').read_text())['historical_votes_imported']==0
for name in ('audit-pair-001.json','audit-reading-001.json','summary.json','baseline-checks.json'):
 shutil.copy2(run/name,archive/'provenance'/name)
checks=json.loads((run/'baseline-checks.json').read_text())
# Preserve runner result, never relabel its conservative research_goal_proved flag.
now=datetime.datetime.now(datetime.timezone.utc).isoformat()
decision={
 'accepted_at':now,'status':'original_M7_complete_at_symbolic_constructive_selector_strength','candidate_sha256':digest,
 'evidence_kind':'uniform natural-language symbolic proof plus exact algorithm and terminating verifier specification',
 'controller_assessment':'Acceptance follows from the explicit mathematical constructions and the original roadmap gate. Independent reviews corroborate the checked argument; review votes and finite tests are not proof premises.',
 'original_gate':'All certified optima for requested parameters without raw scan',
 'gate_mapping':[
  {'clause':'Every admissible requested structural class','proof_sections':[2,3,4,5,6],'reason':'Exact prefix arithmetic and full-stabilizer orbit counts establish the residual invariant, one new class per descent and complete zero-residual coverage, including all requested signature intersections.'},
  {'clause':'Exact certified labels and logical witnesses','proof_sections':[7,10],'reason':'Multiplicity-correct transfer enumerators give all lower-weight exclusions, exact distance or NoLogical, and pinning constructs a minimum physical nonboundary witness.'},
  {'clause':'All requested optima and all ties','proof_sections':[8,9,10],'reason':'Finite exact feasibility and strict objective comparisons prove both optimum directions; least-preimage reconstruction retains every distinct winning presentation exactly once.'},
  {'clause':'Empty and excluded answers are certified','proof_sections':[6,8,10],'reason':'Arithmetic replay proves structural completeness, checks failed constraints and winning strict dominators, and certifies emptiness only after feasibility is exhausted.'},
  {'clause':'Without raw support-pair generation','proof_sections':[4,5,6,11],'reason':'Prefix counts use character sums; compact orbit counts multiply independent shift counts; generation retains representatives rather than expanded pair orbits. Action comparisons and requested output remain explicit costs.'},
  {'clause':'Original scope and dependency closure','proof_sections':[1,12,13],'reason':'Every invoked M5/M6 interface is derived explicitly. M8 efficiency and full software/Lean implementation are separate; historical status prose supplies neither an additional gate nor a mathematical premise.'}
 ],
 'internal_unproved_steps':[],
 'final_review_run':run.name,'final_review_roles':['reviewer_a','reviewer_b'],'final_review_verdicts':[r['verdict'] for r in reviews],
 'same_unchanged_candidate_reviewed':True,'historical_votes_imported':0,
 'implementation_boundary':'Archived executable prototype covers only its stated query and reconstruction subset, not every full-theorem constraint and certificate interface.',
 'finite_replay':{'generation_cases':29,'optimization_queries':75,'all_placement_queries':12,'corruption_controls':['missing_class','duplicate_class','wrong_root_count'],'uniform_proof_premise':False},
 'M8':'open: arbitrary-span efficiency is not established','Lean':'not claimed','quantum_code_inequivalence':'not claimed',
 'github_published':False,
 'harness_terminal_status':summary['status'],'harness_research_goal_proved':summary.get('research_goal_proved'),
 'harness_status_note':'The runner intentionally leaves manual acceptance to this decision; its conservative research_goal_proved flag is preserved unchanged.'
}
(archive/'integration-decision.json').write_text(json.dumps(decision,ensure_ascii=False,indent=2)+'\n')
(archive/'status.json').write_text(json.dumps({'status':decision['status'],'candidate_sha256':digest,'audit_run':run.name,'milestone':'M7','implementation_full_contract_claimed':False,'M8':'open','github_published':False},indent=2)+'\n')
p=archive/'PROOF.md';s=p.read_text();s=s.replace('# M7 compact arithmetic selector — final candidate','# M7 compact arithmetic selector — original milestone proof',1).replace('Status: pending fresh independent dual review and controller acceptance.','Status: original M7 accepted at symbolic constructive-selector strength.\nSee integration-decision.json and the two exact-candidate reviews. Author-time statements in the verbatim claim and argument about pending reviews are historical; the candidate itself is unchanged.',1);p.write_text(s)
p=archive/'README.md';s=p.read_text().replace('**Status: final review and controller acceptance pending.**','**Status: original M7 is complete at symbolic constructive-selector strength.**\n\n[Acceptance decision](integration-decision.json) · [Independent review A](reviewer_a.json) · [Independent review B](reviewer_b.json)',1).replace('## Mathematical result under review','## Mathematical result',1).replace('Final acceptance requires review of that entire mathematical construction and its fidelity to this gate.','The two final independent reviews checked this entire mathematical construction and its fidelity to that gate; the controller acceptance decision records the clause-by-clause assessment.');p.write_text(s)
(archive/'provenance/finalize.py').write_bytes(Path(__file__).read_bytes())
files=[]
for p in sorted(archive.rglob('*')):
 if p.is_file() and '__pycache__' not in p.parts and p.name!='archive-manifest.json':files.append({'path':str(p.relative_to(archive)),'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'bytes':p.stat().st_size})
(archive/'archive-manifest.json').write_text(json.dumps({'created_at':now,'candidate_sha256':digest,'files':files},indent=2)+'\n')
print(json.dumps({'status':decision['status'],'candidate_sha256':digest,'archive_files':len(files),'dependency_files':len(manifest['files'])},indent=2))
