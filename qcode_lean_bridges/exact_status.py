#!/usr/bin/env python3
from pathlib import Path
import json, os, sys
out = Path(sys.argv[1] if len(sys.argv) > 1 else 'qcode_exact_bridge')
state = out / '.exact-state'
sources = list((out / 'QExact').glob('Code_*.lean'))
oleans = list((out / 'QExact').glob('Code_*.olean'))
ok = list((state / 'ok').glob('Code_*')) if (state / 'ok').exists() else []
failed = list((state / 'failed').glob('*')) if (state / 'failed').exists() else []
witnesses = 0
if (out / 'exact_witnesses.jsonl').exists():
    with (out / 'exact_witnesses.jsonl').open() as f:
        witnesses = sum(1 for line in f if line.strip())
result = {'lean_sources': len(sources), 'lean_verified': len(ok), 'oleans': len(oleans),
    'failed': len(failed), 'witness_cache_rows': witnesses}
for name in ('generator.pid', 'generator.exit', 'batch.exit'):
    p = state / name
    if p.exists(): result[name.replace('.', '_')] = p.read_text().strip()
pid = result.get('generator_pid')
if pid: result['generator_running'] = Path(f'/proc/{pid}').exists()
print(json.dumps(result, ensure_ascii=False, indent=2))
if failed:
    print('failed modules:', ', '.join(p.name for p in failed[:20]))
