"""Test parallel k-screening correctness and speedup."""
import sys
from pathlib import Path


# Ensure project root is importable
sys.path.insert(0, str(Path(__file__).parent.parent))

from evaluation.evaluator import evaluate_batch_milp, evaluate_batch_milp_parallel


def test_correctness():
    """Parallel results match sequential results."""
    ell, m = 12, 6
    test_candidates = [
        ([(3,0),(0,1),(0,2)], [(0,3),(1,0),(2,0)]),   # [[144,12,12]] gross
        ([(6,0),(0,1),(0,2)], [(0,3),(2,0),(4,0)]),   # scaled
        ([(1,0),(0,1),(0,2)], [(0,3),(1,0),(2,0)]),   # another
        ([(5,0),(0,1),(0,3)], [(0,3),(1,0),(4,0)]),   # another
        ([(3,0),(0,2),(0,4)], [(0,3),(1,0),(2,0)]),   # another
    ]

    # Sequential
    seq_results = evaluate_batch_milp(ell, m, test_candidates, quick=True)

    # Parallel
    tasks = [(ell, m, A, B) for A, B in test_candidates]
    par_results = evaluate_batch_milp_parallel(tasks, quick=True, max_workers=4)

    # Build lookup for sequential (it sorts by score)
    seq_by_key = {}
    for r in seq_results:
        key = (r["ell"], r["m"],
               tuple(tuple(t) for t in r["A_terms"]),
               tuple(tuple(t) for t in r["B_terms"]))
        seq_by_key[key] = r

    for r in par_results:
        key = (r["ell"], r["m"],
               tuple(tuple(t) for t in r["A_terms"]),
               tuple(tuple(t) for t in r["B_terms"]))
        s = seq_by_key[key]
        assert r["k"] == s["k"], f"k mismatch: {r['k']} vs {s['k']}"
        assert r["n"] == s["n"], f"n mismatch"
        assert r["d"] == s["d"], f"d mismatch: {r['d']} vs {s['d']}"
        assert r["stage"] == s["stage"], f"stage mismatch: {r['stage']} vs {s['stage']}"
        print(f"  [[{r['n']},{r['k']},{r['d']}]] stage={r['stage']} OK")

    print("Correctness: PASS")


if __name__ == "__main__":
    test_correctness()
