"""Bounded, untrusted source-header references from imported local M5/M6/M7/M8 modules.

This is deliberately not a Lean parser. Headers are conservative excerpts; no
elaboration or proof acceptance depends on them. Stop before implementation
syntax and label incomplete excerpts explicitly.
"""
import hashlib
import json
from pathlib import Path
import re

DECL = re.compile(r'^(?:(?:noncomputable|private|protected|partial)\s+)*(?:theorem|lemma|def|abbrev|opaque|instance)\b')
MODULE = re.compile(r'[A-Za-z_][A-Za-z0-9_\x27]*(?:\.[A-Za-z_][A-Za-z0-9_\x27]*)*\Z')
COMMAND = re.compile(r'^(?:namespace|section|end|import|open|variable|universe|attribute|set_option|#)\b')
STOP = re.compile(r':=|\b(?:by|where)\b|^\s*\|', re.M)


def _without_comments(source):
    """Remove nested Lean comments while retaining line boundaries; mask string contents."""
    out, i, depth, string = [], 0, 0, False
    while i < len(source):
        pair = source[i:i+2]
        if depth:
            if pair == '/-': depth += 1; out.extend('  '); i += 2; continue
            if pair == '-/': depth -= 1; out.extend('  '); i += 2; continue
            out.append('\n' if source[i] == '\n' else ' '); i += 1; continue
        if not string and pair == '/-': depth = 1; out.extend('  '); i += 2; continue
        if not string and pair == '--':
            end = source.find('\n', i)
            if end < 0: out.extend(' ' * (len(source)-i)); break
            out.extend(' ' * (end-i)); i = end; continue
        if source[i] == '"' and (i == 0 or source[i-1] != '\\'): string = not string
        out.append(('\n' if source[i] == '\n' else ' ') if string else source[i]); i += 1
    return ''.join(out)


def local_interfaces(project, imports, fingerprints, *, max_files=64, max_source_bytes=2000000,
                     max_chars=24000, max_entries=256, max_header_chars=2400, max_prompt_chars=48000):
    if max_prompt_chars < 1024:
        raise ValueError('local interface prompt budget must be at least 1024 characters')
    root = Path(project).resolve()
    queue, seen, files, entries, skipped = list(imports), set(), [], [], []
    used_bytes = used_chars = 0
    truncated = False
    while queue:
        module = queue.pop(0)
        if len(module) > 200 or module in seen or not MODULE.fullmatch(module) or not module.startswith(('M5', 'M6', 'M7', 'M8')):
            continue
        seen.add(module)
        relative = module.replace('.', '/') + '.lean'
        path = root / relative
        if relative not in fingerprints or not path.is_file() or path.is_symlink() or not path.resolve().is_relative_to(root):

            if len(skipped) < 32: skipped.append({'module': module[:200], 'reason': 'not a fingerprinted local source'})
            continue
        if len(files) >= max_files or path.stat().st_size > max_source_bytes-used_bytes:
            truncated = True
            if len(skipped) < 32: skipped.append({'module': module[:200], 'reason': 'source bound'})
            continue
        raw = path.read_bytes(); used_bytes += len(raw)
        source_hash = hashlib.sha256(raw).hexdigest()
        if source_hash != fingerprints[relative]:
            raise ValueError('local interface source changed after project fingerprint')
        source = _without_comments(raw.decode('utf-8'))
        lines = source.splitlines()
        files.append({'module': module, 'path': relative, 'source_sha256': source_hash})
        for line in lines:
            if line.startswith('import '):
                queue.extend(x for x in line[7:].split() if MODULE.fullmatch(x))
        scopes, i = [], 0
        while i < len(lines):
            line = lines[i]
            if line.startswith('namespace '): scopes.append(('namespace', line[10:].strip()[:200]))
            elif line == 'section' or line.startswith('section '): scopes.append(('section', ''))
            elif line == 'end' or line.startswith('end '):
                if scopes: scopes.pop()
            if not DECL.match(line): i += 1; continue
            start, parts, complete = i+1, [], False
            while i < len(lines):
                current = lines[i]
                if parts and (DECL.match(current) or COMMAND.match(current)):
                    break
                stop = STOP.search(current)
                parts.append(current[:stop.start()] if stop else current)
                i += 1
                if stop:
                    complete = current[stop.start():].startswith(':=')
                    break
                if sum(len(x)+1 for x in parts) >= max_header_chars:
                    break
            header = '\n'.join(parts).strip()
            # A first := may belong to a let/type term or a default binder.
            # In those cases this is only an excerpt, not the full type.
            if re.search(r'\b(?:let|have|do|match)\b', header) or any(
                    header.count(left) != header.count(right) for left,right in [('(',')'),('[',']'),('{','}')]):
                complete = False
            if len(header) > max_header_chars:
                header = header[:max_header_chars]; complete = False
            if len(entries) >= max_entries or used_chars + len(header) > max_chars:
                truncated = True; continue
            used_chars += len(header)
            entries.append({'module': module, 'line': start,
                            'namespace_context': [name for kind,name in scopes if kind == 'namespace'][-16:],
                            'header': header, 'complete_header': complete,
                            'note': 'source header, not elaborated; implementation omitted' if complete else
                                    'incomplete source-header excerpt; do not infer missing type text'})
    result = {'kind': 'untrusted_local_source_header_references', 'files': files, 'entries': entries,
            'truncated': truncated, 'skipped': skipped,
            'limits': {'files': max_files, 'source_bytes': max_source_bytes, 'header_chars': max_chars,
                       'entries': max_entries, 'per_header_chars': max_header_chars, 'prompt_chars': max_prompt_chars}}
    while len(json.dumps(result, ensure_ascii=False)) > max_prompt_chars and entries:
        entries.pop(); result['truncated'] = True
    while len(json.dumps(result, ensure_ascii=False)) > max_prompt_chars and skipped:
        skipped.pop(); result['truncated'] = True
    while len(json.dumps(result, ensure_ascii=False)) > max_prompt_chars and files:
        files.pop(); result['truncated'] = True
    # If the provenance itself exhausts the budget, all headers were removed first.
    return result
