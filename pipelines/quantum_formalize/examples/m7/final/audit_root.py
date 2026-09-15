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

SOURCE_SHA = '8ad32a3432f4b7fd3ad15aa4467e0f01255ce593ac9e474b1af38c9424addf19'
CANDIDATE_SHA = '44e9358d34dd671ce76b39cd5c1f64b6a16b5229b9d98ce0e21d813b557c7a99'
DECISION_SHA = '9ac58f77eeaba9651a62d89094ce02f7ea7d2475b594814e1f76bfd5fd44ff26'
SECTIONS = ['ActionSignature', 'Canonical', 'Generation', 'Selector',
            'PhysicalLabels', 'Replay', 'Resources', 'PresentationExtensions']
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
        self.base = self.repo / 'pipelines/quantum_formalize/examples/m7'
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
        require('original_m7' in root['nodes'], 'final: missing complete root target')
        final_node = root['nodes']['original_m7']
        require(final_node['spec']['name'] == 'M7.Final.original_m7' and
                final_node['spec']['statement'] == 'M7.Final.OriginalM7', 'wrong complete M7 root identity')
        require(final_node['dependencies'] == [s.lower() for s in SECTIONS], 'root section dependency mismatch')
        root_info = self.target('final', 'original_m7')

        source = read(self.base / 'SOURCE.json')
        require(source['source_sha256'] == SOURCE_SHA and source['candidate_sha256'] == CANDIDATE_SHA,
                'SOURCE metadata differs from original frozen M7 source')
        proof_path = self.repo / source['source']
        decision_path = self.repo / source['natural_acceptance']
        require(sha(proof_path) == SOURCE_SHA and sha(decision_path) == DECISION_SHA,
                'frozen natural-language proof/decision changed')
        candidate = read(proof_path.parent / 'candidate.json')
        canonical_candidate = hashlib.sha256(json.dumps(candidate, sort_keys=True, ensure_ascii=False,
                                                       separators=(',', ':')).encode()).hexdigest()
        require(canonical_candidate == CANDIDATE_SHA, 'frozen natural-language candidate changed')
        require(read(decision_path)['candidate_sha256'] == CANDIDATE_SHA, 'source decision/candidate mismatch')

        prep = need(self.final / 'prepare.py')
        constants = {}
        for stmt in ast.parse(prep.read_text()).body:
            if isinstance(stmt, ast.Assign):
                for target in stmt.targets:
                    if isinstance(target, ast.Name) and target.id in {'sections', 'aliases'}:
                        constants[target.id] = ast.literal_eval(stmt.value)
        require(set(constants) == {'sections', 'aliases'}, 'cannot read frozen root claim selection')
        sections, aliases = constants['sections'], constants['aliases']
        require(list(sections) == SECTIONS, 'complete original root section map changed')
        claims = read(self.final / 'CLAIM_MAP.json')
        require(list(claims) == SECTIONS, 'CLAIM_MAP section identity mismatch')
        source_text = ''.join('import ' + v + '\n' for v in aliases.values()) + '\nnamespace M7.Final\n'
        claim_receipts = []
        for section, batches in sections.items():
            expected_claims = []
            clauses = []
            for batch, selected in batches.items():
                data = self.batch(batch)
                chosen = list(data['nodes']) if selected == 'all' else selected
                for node_id in chosen:
                    info = self.target(batch, node_id)
                    expected_claims.append({'batch': batch, 'target': info['target'],
                        'receipt': str((data['root'] / 'result.json').relative_to(self.repo)),
                        'statement': info['statement']})
                    clauses.append('(' + info['statement'] + ')')
                    claim_receipts.append(info)
                accepted_source = self.final / 'lean' / (aliases[batch] + '.lean')
                require(sha(accepted_source) == sha(data['root'] / 'AcceptedExperiment.lean'),
                        f'{batch}: final imported accepted source does not match canonical assembly')
                require(root['environment'].get(accepted_source.name) == sha(accepted_source),
                        f'{batch}: final imported proof source differs from frozen environment')
            require(claims[section] == expected_claims, f'{section}: CLAIM_MAP/parent target mismatch')
            section_node = root['nodes'][section.lower()]
            require(section_node['spec']['name'] == 'M7.Final.' + section.lower() and
                    section_node['spec']['statement'] == 'M7.Final.' + section,
                    f'{section}: final section target mismatch')
            source_text += '\n/-- Exact frozen original-scope clauses; no correctness proposition is an input. -/\nnoncomputable def ' + section + ' : Prop :=\n  ' + ' ∧\n  '.join(clauses) + '\n'
        source_text += '\nnoncomputable def OriginalM7 : Prop :=\n  ' + ' ∧ '.join(SECTIONS) + '\nend M7.Final\n'
        final_source = need(self.final / 'lean/M7Final.lean')
        require(final_source.read_text() == source_text, 'final closed claim definitions differ from CLAIM_MAP composition')
        require(root['environment'].get('M7Final.lean') == sha(final_source), 'final claim source changed after freezing')
        for filename, expected_hash in root['environment'].items():
            exported = self.final / 'lean' / filename if filename.endswith('.lean') else self.final / filename
            if exported.is_file():
                require(sha(exported) == expected_hash, f'final exported environment mismatch: {filename}')
        return {'status': 'accepted', 'm7_formalized': True,
                'audited_at_utc': datetime.now(timezone.utc).isoformat(),
                'audit_kind': 'read-only canonical exact-target and provenance verification',
                'audit_script_sha256': sha(Path(__file__).resolve()),
                'root': root_info, 'root_manifest_sha256': sha(root['root'] / 'MANIFEST.json'),
                'root_result_sha256': sha(root['root'] / 'result.json'),
                'claims_sha256': sha(final_source), 'claim_map_sha256': sha(self.final / 'CLAIM_MAP.json'),
                'source_metadata_sha256': sha(self.base / 'SOURCE.json'),
                'source_sha256': SOURCE_SHA, 'candidate_sha256': CANDIDATE_SHA,
                'natural_decision_sha256': DECISION_SHA,
                'verified_clause_count': len(claim_receipts), 'verified_claim_targets': claim_receipts,
                'verified_batches': {name: {'files': len(data['manifest']),
                    'manifest_sha256': sha(data['root'] / 'MANIFEST.json'),
                    'result_sha256': sha(data['root'] / 'result.json')} for name, data in self.batches.items()},
                'new_models_or_compilation_started': False, 'additional_scope_gate': False}

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--repo', type=Path, default=Path(__file__).resolve().parents[5])
    parser.add_argument('--check-only', action='store_true', help='Even on success, do not write ROOT_ACCEPTANCE.json.')
    args = parser.parse_args()
    final = args.repo / 'pipelines/quantum_formalize/examples/m7/final'
    try:
        # Missing root is normal pending work; do not import the prover runtime first.
        need(final / 'experiment/MANIFEST.json')
        result = Audit(args.repo).run()
        if not args.check_only:
            (final / 'ROOT_ACCEPTANCE.json').write_text(json.dumps(result, ensure_ascii=False, indent=2) + '\n')
        print(json.dumps({'status': result['status'], 'm7_formalized': True,
                          'verified_clause_count': result['verified_clause_count'],
                          'acceptance_written': not args.check_only}, ensure_ascii=False))
        return 0
    except Pending as error:
        print(json.dumps({'status': 'pending', 'm7_formalized': False, 'reason': str(error),
                          'acceptance_written': False}, ensure_ascii=False))
        return 2
    except (Invalid, KeyError, ValueError, OSError, TypeError) as error:
        print(json.dumps({'status': 'invalid_evidence', 'm7_formalized': False, 'reason': str(error),
                          'acceptance_written': False}, ensure_ascii=False))
        return 3

if __name__ == '__main__':
    raise SystemExit(main())
