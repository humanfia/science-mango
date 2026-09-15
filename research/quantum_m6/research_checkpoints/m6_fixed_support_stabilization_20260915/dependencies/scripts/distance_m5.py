#!/usr/bin/env python3
"""Exact logical distances for explicit M5 cyclic CSS constructions (python-sat).

No distance lower bound is an input. Both cyclic translation anchors must be
UNSAT at weight d-1; SAT witnesses are checked by independent row reduction.
Zero-logical-qubit codes have no logical distance in this convention.
"""
import argparse
import hashlib
import json
import threading
import time
from pathlib import Path

from pysat.card import CardEnc, EncType
from pysat.formula import CNF, IDPool
from pysat.solvers import Solver


def basis(rows):
    result = {}
    for v in rows:
        while v:
            p = v.bit_length() - 1
            if p not in result:
                result[p] = v
                break
            v ^= result[p]
    return result


def reduce(v, rows):
    for p in sorted(rows, reverse=True):
        if v >> p & 1:
            v ^= rows[p]
    return v


def nullspace(rows, n):
    b = basis(rows)
    result = []
    for f in range(n):
        if f in b:
            continue
        v = 1 << f
        for p in sorted(b):
            if (v & b[p]).bit_count() % 2:
                v |= 1 << p
        result.append(v)
    assert all((r & v).bit_count() % 2 == 0 for r in rows for v in result)
    return result


def css(n, a, b):
    for support in (a, b):
        if not support or len(set(support)) != len(support) or any(x < 0 or x >= n for x in support):
            raise ValueError('Supports must be nonempty distinct residues in [0,N)')
    def circ(s, sign):
        return [sum(1 << ((i + sign * j) % n) for j in s) for i in range(n)]
    hx = [x | (y << n) for x, y in zip(circ(a, 1), circ(b, 1))]
    hz = [x | (y << n) for x, y in zip(circ(b, -1), circ(a, -1))]
    assert all((x & z).bit_count() % 2 == 0 for x in hx for z in hz)
    # Explicitly check the involution giving d_X = d_Z.
    def dual(v):
        return sum(1 << ((1 - i // n) * n + (-i % n)) for i in range(2*n) if v >> i & 1)
    assert {dual(x) for x in hx} == set(hz)
    return hx, hz


def logicals(hx, hz, n):
    extended = basis(hz)
    result = []
    for v in nullspace(hx, n):
        remainder = reduce(v, extended)
        if remainder:
            extended[remainder.bit_length() - 1] = remainder
            result.append(v)
    assert len(result) == n - len(basis(hx)) - len(basis(hz))
    return result


def xor(cnf, literals, pool):
    out = literals[0]
    for v in literals[1:]:
        prev, out = out, pool.id()
        cnf.extend([[prev, v, -out], [-prev, -v, -out], [prev, -v, out], [-prev, v, out]])
    return out


def instance(n, hz, logical, bound, anchor):
    cnf, pool = CNF(), IDPool(start_from=2*n+1)
    def parity(v):
        return xor(cnf, [i+1 for i in range(2*n) if v >> i & 1], pool)
    for row in hz:
        cnf.append([-parity(row)])
    cnf.append([parity(v) for v in logical])
    if anchor == 'left':
        cnf.append([1])
    elif anchor == 'right_only':
        cnf.extend([[-i] for i in range(1, n+1)])
        cnf.append([n+1])
    else:
        raise ValueError(anchor)
    cnf.extend(CardEnc.atmost(list(range(1, 2*n+1)), bound, vpool=pool, encoding=EncType.kmtotalizer).clauses)
    return cnf


def query(n, hx, hz, logical, bound, anchor, timeout, save=None):
    start = time.monotonic()
    cnf = instance(n, hz, logical, bound, anchor)
    with Solver(name='glucose42', bootstrap_with=cnf, with_proof=save is not None) as solver:
        timer = threading.Timer(timeout, solver.interrupt)
        timer.start()
        try:
            outcome = solver.solve_limited(expect_interrupt=True)
        finally:
            timer.cancel()
            timer.join()
        witness = None
        if outcome is True:
            model = set(solver.get_model())
            witness = [i for i in range(2*n) if i+1 in model]
            v = sum(1 << i for i in witness)
            assert len(witness) <= bound
            assert all((v & row).bit_count() % 2 == 0 for row in hz)
            assert reduce(v, basis(hx)) != 0
        if outcome is False and save is not None:
            cnf.to_file(str(save) + '.cnf')
            Path(str(save) + '.drat').write_text('\n'.join(solver.get_proof()) + '\n')
    return dict(bound=bound, anchor=anchor, status='sat' if outcome is True else 'unsat' if outcome is False else 'unknown', witness=witness, seconds=time.monotonic()-start)


def distance(record, timeout=30, max_weight=32, proof_dir=None):
    n, a, b = record['N'], record['A'], record['B']
    hx, hz = css(n, a, b)
    logical = logicals(hx, hz, 2*n)
    out = dict(record, n=2*n, k=len(logical), rank_hx=len(basis(hx)), rank_hz=len(basis(hz)), queries=[])
    if 'F' in record:
        assert out['k'] == 2*(record['F'].bit_length()-1)
    if not logical:
        return dict(out, status='no_logical_qubits', distance=None)
    upper_vectors = [v for v in nullspace(hz, 2*n) if reduce(v, basis(hx))]
    upper_v = min(upper_vectors, key=int.bit_count)
    upper = upper_v.bit_count()
    witness = [i for i in range(2*n) if upper_v >> i & 1]
    lower = 1
    for bound in range(1, min(max_weight, upper)+1):
        results = [query(n, hx, hz, logical, bound, anchor, timeout) for anchor in ('left', 'right_only')]
        out['queries'].extend(results)
        if all(r['status'] == 'unsat' for r in results):
            lower = bound+1
        for r in results:
            if r['witness'] is not None and len(r['witness']) <= upper:
                witness, upper = r['witness'], len(r['witness'])
        if lower == upper:
            break
        if any(r['status'] == 'unknown' for r in results):
            break
    out.update(status='exact' if lower == upper else 'bounds', d_lower=lower, d_upper=upper, distance=upper if lower == upper else None, x_witness=witness)
    if lower == upper and proof_dir is not None:
        proof_dir.mkdir(parents=True, exist_ok=True)
        out['lower_bound_replays'] = [query(n, hx, hz, logical, upper-1, anchor, timeout, proof_dir/anchor) for anchor in ('left', 'right_only')]
        assert all(r['status'] == 'unsat' for r in out['lower_bound_replays'])
    return out


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--input', type=Path, default=Path('research_checkpoints/period_residue_arithmetic_law_reviewed/verification/test-results.json'))
    parser.add_argument('--output', type=Path, default=Path('research_checkpoints/m5_distance_20260915/results.json'))
    parser.add_argument('--timeout', type=float, default=30)
    parser.add_argument('--max-weight', type=int, default=32)
    args = parser.parse_args()
    records = json.loads(args.input.read_text())['examples']
    output = dict(input=str(args.input), input_sha256=hashlib.sha256(args.input.read_bytes()).hexdigest(), solver='python-sat/glucose42', results=[])
    args.output.parent.mkdir(parents=True, exist_ok=True)
    for index, record in enumerate(records):
        result = distance(record, args.timeout, args.max_weight, args.output.parent/'proofs'/str(index))
        output['results'].append(result)
        args.output.write_text(json.dumps(output, indent=2)+'\n')
        print(json.dumps({key: result.get(key) for key in ('N','k','distance','status','d_lower','d_upper')}), flush=True)


if __name__ == '__main__':
    main()
