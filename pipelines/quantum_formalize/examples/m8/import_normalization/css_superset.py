"""Exact accepted-source import normalization, only for unfrozen new children.

Read-only audit proves the complete M6ActualCSSAccepted import closure is supplied
by M6FinalDependencies with identical declaration types AND proof bodies, and
identical definition source files. No canonical parent is ever changed.
"""
from pathlib import Path
import hashlib
import json
import re
from pipelines.quantum_formalize.accepted_order import _parts


def sha(data):
    if isinstance(data, Path):
        data = data.read_bytes()
    if isinstance(data, str):
        data = data.encode()
    return hashlib.sha256(data).hexdigest()


def read(path):
    return json.loads(path.read_text())


def canonical(stage, cache):
    stage = stage.resolve()
    if stage in cache:
        return cache[stage]
    e = stage / 'experiment'
    r = read(e / 'result.json')
    assert r['status'] == 'finished' and all(r.get(k) is True for k in
        ('assembly_accepted', 'environment_unchanged', 'experiment_passed')), stage
    m = read(e / 'MANIFEST.json')
    m = m.get('files', m)
    for name, digest in m.items():
        assert sha(e / name) == digest, (stage, name)
    result = {'stage': str(stage), 'manifest_sha256': sha(e / 'MANIFEST.json'),
        'manifest_files_verified': len(m), 'result_sha256': sha(e / 'result.json'),
        'environment': read(e / 'environment.json')}
    cache[stage] = result
    return result


def closure(stage, root, cache, aliases=None):
    audit = canonical(stage, cache)
    aliases = aliases or {}
    seen = {}
    def walk(name):
        if name in seen:
            return
        path = aliases.get(name, stage / 'lean' / (name + '.lean'))
        if not path.exists():
            assert name.startswith('Mathlib'), ('unresolved local import', name)
            return
        if name not in aliases:
            assert audit['environment'].get(path.name) == sha(path), (stage, path)
        text = path.read_text()
        seen[name] = {'path': path, 'text': text, 'sha256': sha(path)}
        for line in re.findall(r'(?m)^\s*import\s+([^\n]+)', text):
            for dep in line.split():
                walk(dep)
    walk(root)
    return seen


def split_modules(modules):
    theorems, definitions, import_only = {}, {}, {}
    for name, info in modules.items():
        parts = _parts(info['text'])
        if parts:
            for theorem, declaration in parts[1].items():
                assert theorem not in theorems, ('duplicate declaration', theorem)
                theorems[theorem] = (name, declaration)
        elif all(not line.strip() or re.fullmatch(r'import [A-Za-z0-9_.]+', line)
                 for line in info['text'].splitlines()):
            import_only[name] = info
        else:
            assert not re.search(r'(?m)^theorem ', info['text']), ('unparsed container', name)
            definitions[name] = info
    return theorems, definitions, import_only


def audit(repo):
    repo = Path(repo).resolve()
    base = repo / 'pipelines/quantum_formalize/examples'
    wanted_stage, provided_stage = base/'m6/actual_css', base/'m8/physical_bridge'
    cache = {}
    wanted = closure(wanted_stage, 'M6ActualCSSAccepted', cache,
        {'M6ActualCSSAccepted': wanted_stage/'experiment/AcceptedExperiment.lean'})
    provided = closure(provided_stage, 'M6FinalDependencies', cache)
    wt, wd, wi = split_modules(wanted)
    pt, pd, _ = split_modules(provided)
    assert not (wt.keys() - pt.keys()), ('missing theorems', wt.keys()-pt.keys())
    assert not (wd.keys() - pd.keys()), ('missing definitions', wd.keys()-pd.keys())
    for name in wd:
        assert wd[name]['text'] == pd[name]['text'], ('definition source mismatch', name)
    # The existing M6 final promotion records exact receipts and proof hashes.
    final = base/'m6/final'
    promotion = read(final/'DEPENDENCY_IMPORT.json')
    assert promotion['accepted']
    assert promotion['source_sha256'] == sha(final/'lean/M6FinalDependencies.lean')
    base_parts = _parts((final/'lean/M6FinalDependencies.lean').read_text())
    assert base_parts
    for name, declaration in base_parts[1].items():
        assert name in pt and declaration == pt[name][1], ('superset changed promoted proof', name)
    origins = {row['name']: row for row in promotion['theorems']}
    baseline = {}
    for entry in read(final/'BASELINE_PROOF_IMPORTS.json'):
        path = repo/entry['canonical']
        assert sha(path) == entry['sha256'], path
        stage = path.parent.parent
        canonical(stage, cache)
        parts = _parts(path.read_text())
        assert parts
        for name, declaration in parts[1].items():
            baseline[name] = (stage, declaration)
    rows = []
    for name, (source_module, declaration) in sorted(wt.items()):
        target_module, target_decl = pt[name]
        assert declaration == target_decl, ('declaration type/proof mismatch', name)
        statement, proof = declaration.split(' := by', 1)
        if name in origins:
            origin = origins[name]
            assert origin['declaration_sha256'] == sha(declaration), name
            stage = base/'m6'/origin['stage'].removesuffix('/experiment')
            canonical(stage, cache)
            for pathkey, hashkey in [('receipt','receipt_sha256'),
                    ('candidate','source_sha256'),('target','target_sha256')]:
                assert sha(base/'m6'/origin[pathkey]) == origin[hashkey], (name,pathkey)
            receipt_path = base/'m6'/origin['receipt']
        else:
            assert name in baseline and baseline[name][1] == declaration, ('no origin',name)
            stage = baseline[name][0]
            matches = []
            for spec in (stage/'experiment/nodes').glob('*/resolved-spec.json'):
                if read(spec)['name'] == name:
                    matches.append(spec.parent/'receipt.json')
            assert len(matches) == 1, (name,matches)
            receipt_path = matches[0]
        receipt = read(receipt_path)
        assert receipt['accepted'] is True and receipt['result']['accepted'] is True, name
        assert receipt['result']['target'] == name, name
        successful = [v for v in receipt['result']['attempts'] if v.get('accepted')]
        assert len(successful) == 1, (name, 'ambiguous successful attempt')
        verification = successful[0]
        assert set(verification['axioms']) <= {'propext','Classical.choice','Quot.sound'}, name
        raw = stage/'experiment/node_runs'/receipt_path.parent.name
        for source_key, hash_key in [('proof_path','source_sha256'),('target_path','target_sha256')]:
            candidates = list(raw.rglob(Path(verification[source_key]).name))
            assert candidates and all(sha(f) == verification[hash_key] for f in candidates), (name,source_key)
        node = receipt_path.parent
        spec = read(node/'resolved-spec.json')
        assert spec['name'] == name and ('theorem '+name+' : '+spec['statement']) == statement, name
        assert (node/'declaration.lean.txt').read_text().strip() == declaration, name
        rows.append({'name':name, 'wanted_module':source_module,
            'provided_module':target_module, 'statement_sha256':sha(statement),
            'proof_sha256':sha(proof), 'declaration_sha256':sha(declaration),
            'receipt':str(receipt_path.relative_to(repo)), 'receipt_sha256':sha(receipt_path),
            'candidate_source_sha256':verification['source_sha256'],
            'frozen_target_sha256':verification['target_sha256'],
            'axioms':verification['axioms'],
            'exact_type_and_proof_body_match':True})
    return {'accepted':True, 'purpose':'accepted import-container deduplication only; not a new mathematical gate',
        'wanted_root':'M6ActualCSSAccepted', 'provided_root':'M6FinalDependencies',
        'theorem_count':len(rows), 'provided_theorem_count':len(pt),
        'definition_file_count':len(wd), 'theorems':rows,
        'definitions':[{'module':n,'wanted_sha256':wd[n]['sha256'],'provided_sha256':pd[n]['sha256']}
                       for n in sorted(wd)],
        'import_only_containers':[{'module':n,'sha256':v['sha256']} for n,v in wi.items()],
        'wanted_source_sha256':wanted['M6ActualCSSAccepted']['sha256'],
        'provided_closure':[{'module':n,'sha256':v['sha256']} for n,v in sorted(provided.items())],
        'canonical_sources':[{k:v for k,v in entry.items() if k!='environment'} for entry in cache.values()],
        'promotion_record_sha256':sha(final/'DEPENDENCY_IMPORT.json'),
        'baseline_record_sha256':sha(final/'BASELINE_PROOF_IMPORTS.json')}


def normalize_child(repo, project, published_lean, report_path):
    """Call after parent promotion and BEFORE any child proof environment is frozen."""
    project, published_lean, report_path = map(lambda p: Path(p).resolve(),
        (project, published_lean, report_path))
    repo = Path(repo).resolve()
    assert project != repo and 'experiment' not in project.parts
    assert not project.is_relative_to(repo/'pipelines/quantum_formalize/examples'), 'Project must be an isolated child checkout'
    assert 'experiment' not in published_lean.parts
    assert not (published_lean.parent/'experiment/MANIFEST.json').exists(), 'Refusing a canonical published parent or child'
    assert not list(project.glob('.humanize-formal-runs/*/experiment/environment.json')), \
        'Refusing to modify a frozen/running child environment'
    record = audit(repo)
    for row in record['provided_closure']:
        path = project/(row['module']+'.lean')
        assert path.exists() and sha(path) == row['sha256'], ('child superset mismatch',path)
    original = project/'M6ActualCSSAccepted.lean'
    shim = 'import M6FinalDependencies\n'
    if original.exists():
        assert sha(original) in {record['wanted_source_sha256'],sha(shim)}, original
    # Retain the original source identity in the report, never alter a parent package.
    for directory in (project,published_lean):
        directory.mkdir(parents=True,exist_ok=True)
        (directory/'M6ActualCSSAccepted.lean').write_text(shim)
    record['child_normalization']={'project':str(project),'published_lean':str(published_lean),
        'shim_module':'M6ActualCSSAccepted','shim_sha256':sha(shim),
        'shim_contents':shim,'child_compile_and_normal_acceptance_still_required':True}
    report_path.parent.mkdir(parents=True,exist_ok=True)
    report_path.write_text(json.dumps(record,indent=2)+'\n')
    return record
