#!/usr/bin/env python3
"""Read-only evidence audit; write ROOT_ACCEPTANCE.json only after every check passes.

Run with the harness Python from the repository. No model, compiler, review vote,
or new mathematical acceptance condition is introduced by this script.
"""
import sys
sys.dont_write_bytecode = True
import argparse
import ast
from datetime import datetime, timezone
import hashlib
import json
import re
from pathlib import Path

SOURCE_SHA = 'fd39ff50501693e6b53e63ed7894079b5b460ebe19bca306d225282dc8e3fd91'
CANDIDATE_SHA = '94f42a9b7a9f01e55ed787c461828c567e258dc24276eeda33e03a62cffab008'
DECISION_SHA = '0eaacc204ca496c1e50f869c532e53f51af68c22c6ce3ff22b916fe8bbbbff13'
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}

class Pending(Exception):
    pass

class Invalid(Exception):
    pass

def require(condition, reason):
    if not condition:
        raise Invalid(reason)

def need(path):
    if not path.is_file():
        raise Pending(f'missing evidence: {path}')
    return path

def read(path):
    return json.loads(need(path).read_text())

def sha(path):
    return hashlib.sha256(need(path).read_bytes()).hexdigest()

class Audit:
    def __init__(self, repo):
        self.repo = repo.resolve()
        self.base = self.repo / 'pipelines/quantum_formalize/examples/m8'
        self.final = self.base / 'final'
        self.batches = {}
        self.targets = {}
        sys.path.insert(0, str(self.repo))
        from pipelines.quantum_formalize.engine import Spec, digest, render, check_axiom_output
        from pipelines.quantum_formalize.dag_runner import portable_declaration, proof_context
        self.Spec, self.digest, self.render = Spec, digest, render
        self.portable, self.context, self.axioms = portable_declaration, proof_context, check_axiom_output

    def batch(self, name):
        if name in self.batches:
            return self.batches[name]
        root = self.base / name / 'experiment'
        manifest_raw = read(root / 'MANIFEST.json')
        manifest = manifest_raw.get('files', manifest_raw)
        require(isinstance(manifest, dict) and bool(manifest), f'{name}: empty manifest')
        if 'file_count' in manifest_raw:
            require(manifest_raw['file_count'] == len(manifest), f'{name}: manifest file count mismatch')
        for rel, expected in manifest.items():
            path = root / rel
            require(path.resolve().is_relative_to(root.resolve()), f'{name}: escaping manifest path')
            require(sha(path) == expected, f'{name}: manifest hash mismatch: {rel}')
        result = read(root / 'result.json')
        if result.get('status') != 'finished' or any(result.get(k) is not True for k in
                ['assembly_accepted', 'environment_unchanged', 'experiment_passed']):
            raise Pending(f'{name}: canonical experiment gates have not all passed')
        graph = read(root / 'graph.json')
        require(result['graph_sha256'] == self.digest(graph), f'{name}: graph receipt hash mismatch')
        state = read(root / 'nodes/state.json')
        nodes = {n['id']: n for n in graph['nodes']}
        require(len(nodes) == len(graph['nodes']), f'{name}: duplicate node identity')
        for node in nodes.values():
            if node.get('spec'):
                require(not node['spec'].get('context', '').strip(), f'{name}: unfrozen graph context')
        build = read(root / 'build.json')
        assembly = read(root / 'assembly-compile.json')
        for label, record in [('build', build), ('assembly', assembly)]:
            require(record.get('returncode') == 0 and record.get('timed_out') is False,
                    f'{name}: {label} receipt not successful')
        data = dict(root=root, manifest=manifest, result=result, graph=graph, nodes=nodes,
                    state=state, environment=read(root / 'environment.json'),
                    assembly=need(root / 'AcceptedExperiment.lean').read_text())
        self.batches[name] = data
        return data

    def target(self, batch, node_id):
        key = (batch, node_id)
        if key in self.targets:
            return self.targets[key]
        b = self.batch(batch)
        require(node_id in b['nodes'], f'{batch}: target node absent: {node_id}')
        node = b['nodes'][node_id]
        require(node.get('spec') is not None, f'{batch}/{node_id}: target is only planned')
        graph_spec = node['spec']
        receipt_path = b['root'] / 'nodes' / node_id / 'receipt.json'
        receipt = read(receipt_path)
        require(receipt == b['state']['nodes'][node_id], f'{batch}/{node_id}: receipt/state mismatch')
        require(receipt.get('accepted') is True and receipt['result'].get('accepted') is True,
                f'{batch}/{node_id}: not accepted')
        result = receipt['result']
        require(result.get('target') == graph_spec['name'], f'{batch}/{node_id}: wrong target identity')
        require(node_id in b['result']['accepted_nodes'], f'{batch}/{node_id}: not in accepted node list')
        deps = {}
        for dep in node.get('dependencies', []):
            self.target(batch, dep)
            deps[dep] = b['state']['nodes'][dep]
        ancestors, context = self.context(deps)
        resolved = read(b['root'] / 'nodes' / node_id / 'resolved-spec.json')
        expected = self.Spec.model_validate(graph_spec).model_copy(update={'context': context})
        inherited = {m for a in ancestors.values() for m in a['payload']['imports']}
        expected = expected.model_copy(update={'imports': sorted(set(expected.imports) | inherited)})
        require(resolved == expected.model_dump(), f'{batch}/{node_id}: resolved exact spec mismatch')
        require(result.get('spec_sha256') == self.digest(resolved), f'{batch}/{node_id}: resolved spec digest mismatch')
        last = result['attempts'][-1]
        require(last.get('accepted') is True and last.get('stage') == 'acceptance',
                f'{batch}/{node_id}: last receipt not full acceptance')
        require(set(last.get('axioms', [])) <= ALLOWED, f'{batch}/{node_id}: nonstandard axioms')
        folder = b['root'] / 'node_runs' / node_id / Path(last['proof_path']).parent.name
        candidate = folder / Path(last['proof_path']).name
        target = folder / Path(last['target_path']).name
        require(sha(candidate) == last['source_sha256'], f'{batch}/{node_id}: candidate source mismatch')
        require(sha(target) == last['target_sha256'], f'{batch}/{node_id}: frozen target source mismatch')
        frozen = ''.join(f'import {x}\n' for x in expected.imports) + '\n' + expected.context + \
            '\ndef QuantumHarnessFrozenTarget : Prop :=\n' + \
            '\n'.join('  ' + line for line in expected.statement.splitlines()) + '\n'
        require(target.read_text() == frozen, f'{batch}/{node_id}: frozen declaration mismatch')
        draft = read(folder / 'draft.json')['proof']
        require(candidate.read_text() == self.render(expected, draft, target.stem),
                f'{batch}/{node_id}: original draft/source mismatch')
        for filename in ['target-compile.json', 'compile.json', 'acceptance-compile.json']:
            log = read(folder / filename)
            require(log.get('returncode') == 0 and log.get('timed_out') is False,
                    f'{batch}/{node_id}: unsuccessful {filename}')
        checker = f'import {candidate.stem}\nexample : QuantumHarnessFrozenTarget := {expected.name}\n#print axioms {expected.name}\n'
        require(need(folder / 'Acceptance.lean').read_text() == checker,
                f'{batch}/{node_id}: exact-target axiom checker mismatch')
        ok, axioms, reason = self.axioms(read(folder / 'acceptance-compile.json')['output'], expected.name)
        require(ok and set(axioms) == set(last['axioms']) and set(axioms) <= ALLOWED,
                f'{batch}/{node_id}: axiom receipt/output mismatch: {reason}')
        artifact = result['artifacts'][node_id]
        payload = artifact['payload']
        # Older accepted batches predate the shared-indent transport repair.
        # Both renderings retain the same separately kernel-checked original draft;
        # accept only either exact historical transport, never an arbitrary theorem.
        legacy_body = draft
        if re.search(r'\bQuantumHarnessFrozenTarget\b', draft):
            legacy_body = ('let QuantumHarnessFrozenTarget : Prop := (\n' +
                '\n'.join('  ' + line for line in expected.statement.splitlines()) +
                '\n)\nchange QuantumHarnessFrozenTarget\n' + legacy_body)
        legacy_declaration = f'theorem {expected.name} : {expected.statement} := by\n' + \
            '\n'.join('  ' + line for line in legacy_body.splitlines())
        expected_payload = {'declaration': payload['declaration'], 'imports': expected.imports,
                            'name': expected.name, 'ancestors': sorted(ancestors),
                            'spec_sha256': self.digest(graph_spec)}
        require(payload['declaration'] in {self.portable(expected, draft), legacy_declaration},
                f'{batch}/{node_id}: portable body is not an exact accepted draft transport')
        require(payload == expected_payload and artifact['sha256'] == self.digest(payload),
                f'{batch}/{node_id}: portable payload identity mismatch')
        require(result['artifacts'] == dict(ancestors, **{node_id: artifact}),
                f'{batch}/{node_id}: dependency artifact closure mismatch')
        require(payload['declaration'] in b['assembly'], f'{batch}/{node_id}: declaration absent from assembly')
        info = {'batch': batch, 'node': node_id, 'target': expected.name,
                'statement': expected.statement, 'receipt_sha256': sha(receipt_path),
                'resolved_spec_sha256': self.digest(resolved), 'payload_sha256': artifact['sha256'],
                'source_sha256': last['source_sha256'], 'target_sha256': last['target_sha256'],
                'axioms': axioms}
        self.targets[key] = info
        return info

    def run(self):
        root = self.batch('final')
        constants = {}
        for stmt in ast.parse(need(self.final/'prepare.py').read_text()).body:
            if isinstance(stmt, ast.Assign):
                for target in stmt.targets:
                    if isinstance(target, ast.Name) and target.id in {'parents','selection'}:
                        constants[target.id] = ast.literal_eval(stmt.value)
        require(set(constants)=={'parents','selection'}, 'Cannot read exact frozen root composition')
        parents, selection = constants['parents'], constants['selection']
        require([x[1] for x in selection] == ['Algorithm','PhysicalParameters','Resources','Storage','CostProjection','AdmittedFamilies','ExcludedFamilies'], 'Original M8 group map differs')
        final_node = root['nodes']['original_m8']
        require(final_node['spec']['name']=='M8.Final.original_m8' and final_node['spec']['statement']=='M8.Final.OriginalM8', 'Wrong root identity')
        require(final_node['dependencies']==[x[0] for x in selection], 'Root dependency mismatch')
        root_info = self.target('final','original_m8')
        source = read(self.base/'SOURCE.json')
        require(source['source_sha256']==SOURCE_SHA and source['candidate_sha256']==CANDIDATE_SHA, 'Frozen source identity mismatch')
        proof_path = self.repo/source['source'];decision_path=self.repo/source['natural_acceptance']
        require(sha(proof_path)==SOURCE_SHA and sha(decision_path)==DECISION_SHA,'Frozen natural proof or acceptance changed')
        candidate=read(proof_path.parent/'records/run-7koxumjf/candidate-1-0.json')
        require(hashlib.sha256(json.dumps(candidate,sort_keys=True,ensure_ascii=False,separators=(',',':')).encode()).hexdigest()==CANDIDATE_SHA,'Candidate changed')
        claim=read(self.final/'PRIMARY_CLAIM.json')
        require(hashlib.sha256(claim['claim'].encode()).hexdigest()==claim['claim_utf8_sha256'],'Main claim hash mismatch')
        require(claim['claim_utf8_sha256']=='5953560522e6ffcfff8ba17758a011b39dfdfcac3986ff7d1809d281598d3949','Main claim changed')
        obligations=read(self.final/'ROOT_OBLIGATIONS.json')
        require(obligations['main_claim_sha256']==claim['claim_utf8_sha256'] and obligations['optional_refined_trialcount_required'] is False,'Original scope boundary changed')
        text=''.join('import '+a+'\n' for _,a in parents)+'\nnamespace M8.Final\n'
        rows=[];receipts=[]
        for node,prop,stage,ids in selection:
            batch=self.batch(stage)
            chosen=[x for x in batch['graph']['nodes'] if ids is None or x['id'] in ids]
            require(bool(chosen) and (ids is None or {x['id'] for x in chosen}==set(ids)), 'Missing selected clauses')
            expressions=[]
            for x in chosen:
                info=self.target(stage,x['id']);spec=x['spec'];path=self.base/stage/'experiment/nodes'/x['id']/'resolved-spec.json'
                expressions.append('('+info['statement']+')');receipts.append(info)
                rows.append({'group':prop,'stage':stage,'id':x['id'],'name':spec['name'],'statement':spec['statement'],'statement_sha256':hashlib.sha256(spec['statement'].encode()).hexdigest(),'canonical_resolved_spec':str(path.relative_to(self.repo)),'resolved_spec_sha256':sha(path)})
            group=root['nodes'][node]
            require(group['spec']['name']=='M8.Final.'+node and group['spec']['statement']=='M8.Final.'+prop,'Wrong root group')
            text+='\n/-- Exact original-scope obligations copied from accepted frozen targets. -/\ndef '+prop+' : Prop :=\n  '+' ∧\n  '.join(expressions)+'\n'
        require(rows==obligations['obligations'],'Root obligation map differs from exact canonical targets')
        text+='\n/-- Revised accepted original M8: exact algorithm, physical output, fixed sequential resources, and explicit admitted/excluded families. -/\ndef OriginalM8 : Prop :=\n  '+' ∧ '.join(x[1] for x in selection)+'\nend M8.Final\n'
        final_source=self.final/'lean/M8Final.lean'
        require(need(final_source).read_text()==text,'Root definitions differ from actual accepted target conjunction')
        require(root['environment']['M8Final.lean']==sha(final_source),'Root definitions changed after freezing')
        for stage,alias in parents:
            source_file=self.final/'lean'/(alias+'.lean')
            require(sha(source_file)==sha(self.batch(stage)['root']/'AcceptedExperiment.lean'),'Root accepted import differs from canonical assembly: '+stage)
            require(root['environment'].get(source_file.name)==sha(source_file),'Root imported source changed after freezing: '+stage)
        for filename,digest in root['environment'].items():
            exported=self.final/'lean'/filename if filename.endswith('.lean') else self.final/filename
            need(exported)
            require(sha(exported)==digest,'Exported root environment mismatch: '+filename)
        # Audit every canonical M8 target; no new mathematical condition is introduced.
        for manifest in self.base.glob('*/experiment/MANIFEST.json'):
            stage=manifest.parent.parent.name
            batch=self.batch(stage)
            for node in batch['nodes'].values():
                if node.get('spec'):self.target(stage,node['id'])
        return {'status':'accepted','m8_formalized':True,'audited_at_utc':datetime.now(timezone.utc).isoformat(),
            'audit_kind':'Read-only canonical exact-target, original-source and proof-transport verification',
            'audit_script_sha256':sha(Path(__file__).resolve()),'root':root_info,
            'root_manifest_sha256':sha(root['root']/'MANIFEST.json'),'root_result_sha256':sha(root['root']/'result.json'),
            'claims_sha256':sha(final_source),'claim_map_sha256':sha(self.final/'ROOT_OBLIGATIONS.json'),
            'source_metadata_sha256':sha(self.base/'SOURCE.json'),'source_sha256':SOURCE_SHA,
            'candidate_sha256':CANDIDATE_SHA,'natural_decision_sha256':DECISION_SHA,
            'verified_clause_count':len(receipts),'verified_claim_targets':receipts,
            'verified_target_count':len(self.targets),
            'verified_batches':{name:{'files':len(data['manifest']),'manifest_sha256':sha(data['root']/'MANIFEST.json'),'result_sha256':sha(data['root']/'result.json')} for name,data in self.batches.items()},
            'resource_model':'Original symbolic sequential binary-operation model with actual fixed allocation; not Lean runtime or machine-code extraction',
            'time_exponent':12,'space_exponent':4,'additional_scope_gate':False,'new_models_or_compilation_started':False}

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--repo', type=Path, default=Path(__file__).resolve().parents[5])
    parser.add_argument('--check-only', action='store_true', help='Even on success, do not write ROOT_ACCEPTANCE.json.')
    args = parser.parse_args()
    final = args.repo / 'pipelines/quantum_formalize/examples/m8/final'
    try:
        # Missing root is normal pending work; do not import the prover runtime first.
        need(final / 'experiment/MANIFEST.json')
        result = Audit(args.repo).run()
        if not args.check_only:
            (final / 'ROOT_ACCEPTANCE.json').write_text(json.dumps(result, ensure_ascii=False, indent=2) + '\n')
        print(json.dumps({'status': result['status'], 'm8_formalized': True,
                          'verified_clause_count': result['verified_clause_count'],
                          'acceptance_written': not args.check_only}, ensure_ascii=False))
        return 0
    except Pending as error:
        print(json.dumps({'status': 'pending', 'm8_formalized': False, 'reason': str(error),
                          'acceptance_written': False}, ensure_ascii=False))
        return 2
    except (Invalid, KeyError, ValueError, OSError, TypeError) as error:
        print(json.dumps({'status': 'invalid_evidence', 'm8_formalized': False, 'reason': str(error),
                          'acceptance_written': False}, ensure_ascii=False))
        return 3

if __name__ == '__main__':
    raise SystemExit(main())
