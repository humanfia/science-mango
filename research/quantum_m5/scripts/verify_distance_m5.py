#!/usr/bin/env python3
"""Replay witnesses, regenerate CNFs and verify saved DRAT refutations."""
import argparse
import hashlib
import json
import math
import subprocess
from pathlib import Path

from pysat.formula import CNF
from distance_m5 import basis, css, instance, logicals, reduce


def rem(a, b):
    while a and a.bit_length() >= b.bit_length():
        a ^= b << (a.bit_length()-b.bit_length())
    return a


def gcd(a, b):
    while b:
        a, b = b, rem(a, b)
    return a


def quotient(a, b):
    q = 0
    while a and a.bit_length() >= b.bit_length():
        shift = a.bit_length()-b.bit_length()
        q ^= 1 << shift
        a ^= b << shift
    assert a == 0
    return q


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--results', type=Path, default=Path('research_checkpoints/m5_distance_20260915/results.json'))
    p.add_argument('--drat-trim', required=True)
    args = p.parse_args()
    data = json.loads(args.results.read_text())
    source = Path(data['input'])
    assert hashlib.sha256(source.read_bytes()).hexdigest() == data['input_sha256']
    inputs = json.loads(source.read_text())['examples']
    assert len(inputs) == len(data['results'])
    verified = []
    for index, (original, record) in enumerate(zip(inputs, data['results'])):
        assert all(record[key] == value for key, value in original.items())
        n = record['N']
        assert math.gcd(n, *record['A'], *record['B']) == 1
        a = sum(1 << e for e in record['A'])
        b = sum(1 << e for e in record['B'])
        f = gcd(gcd(a, b), (1 << n) | 1)
        assert f == record['F']
        assert gcd(a, b) == record['G']
        hx, hz = css(n, record['A'], record['B'])
        k = 2*n-len(basis(hx))-len(basis(hz))
        assert k == record['k'] == 2*(f.bit_length()-1)
        if not k:
            assert record['distance'] is None and record['status'] == 'no_logical_qubits'
            verified.append(dict(N=n, k=k, status='no_logical_qubits'))
            continue
        d = record['distance']
        assert record['status'] == 'exact' and d == record['d_lower'] == record['d_upper']
        support = record['x_witness']
        assert len(support) == len(set(support)) == d
        assert all(0 <= i < 2*n for i in support)
        v = sum(1 << i for i in support)
        assert all((v & z).bit_count() % 2 == 0 for z in hz)
        assert reduce(v, basis(hx))
        qa, qb = quotient(a, record['G']), quotient(b, record['G'])
        quotient_witness = qa | (qb << n)
        assert all((quotient_witness & z).bit_count() % 2 == 0 for z in hz)
        assert reduce(quotient_witness, basis(hx))
        assert d <= quotient_witness.bit_count()
        certificates = []
        for anchor in ('left', 'right_only'):
            path = args.results.parent/'proofs'/str(index)/anchor
            cnf_path, proof_path = Path(str(path)+'.cnf'), Path(str(path)+'.drat')
            expected = instance(n, hz, logicals(hx, hz, 2*n), d-1, anchor)
            assert CNF(from_file=str(cnf_path)).clauses == expected.clauses
            run = subprocess.run([args.drat_trim, str(cnf_path), str(proof_path)], capture_output=True, text=True, timeout=120)
            Path(str(path)+'.verification.txt').write_text(run.stdout+run.stderr)
            assert run.returncode == 0 and 's VERIFIED' in run.stdout, run.stdout+run.stderr
            certificates.append(dict(anchor=anchor, cnf_sha256=hashlib.sha256(cnf_path.read_bytes()).hexdigest(), drat_sha256=hashlib.sha256(proof_path.read_bytes()).hexdigest(), verified=True))
        verified.append(dict(N=n, k=k, d=d, fixed_support_distance_upper_bound=quotient_witness.bit_count(), certificates=certificates))
        print(f'N={n}: [[{2*n},{k},{d}]] witness + both DRAT certificates verified', flush=True)
    receipt = dict(status='all_verified', checker=str(Path(args.drat_trim).resolve()), checker_sha256=hashlib.sha256(Path(args.drat_trim).read_bytes()).hexdigest(), results_sha256=hashlib.sha256(args.results.read_bytes()).hexdigest(), results=verified)
    (args.results.parent/'verification.json').write_text(json.dumps(receipt, indent=2)+'\n')


if __name__ == '__main__':
    main()
