"""Run the LC-equivalence-to-CSS suite on a PBB catalog.

For each record in the input JSONL, runs three checks (see
`evaluation/clifford_equivalence.py` for the underlying implementations):

  1. Hadamard 2-coloring (parity-2-coloring; bipartite-check via
     ``is_equivalently_css``).
  2. Uniform per-block S/H rank check (``is_lc_equivalent_css_group``).
  3. Non-uniform {I,S}/{H,HS} GF(2) exact reduction
     (``verify_uniform_reduction_exact``).

Writes one record per input row to the output JSONL with the
original fields plus the boolean flags ``lc_hadamard``,
``lc_uniform``, ``lc_nonuniform_IS_HS`` and the convenience
``lc_any = lc_hadamard or lc_uniform``.

Example:
    uv run python scripts/run_lc_analysis.py \\
        --input results/campaign7_dedup.jsonl \\
        --output results/campaign7_lc_analysis.jsonl
"""
import argparse
import json
import sys
import time
from concurrent.futures import ProcessPoolExecutor, as_completed
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))


def lc_worker(record_json: str) -> dict:
    """One-record LC analysis. Worker-safe: imports inside function."""
    from evaluation.pbb_code import build_pbb_code
    from evaluation.clifford_equivalence import (
        is_equivalently_css,
        is_lc_equivalent_css_group,
        verify_uniform_reduction_exact,
    )

    r = json.loads(record_json)
    A = [tuple(t) for t in r["A_terms"]]
    B = [tuple(t) for t in r["B_terms"]]
    C = [tuple(t) for t in (r.get("C_terms") or [])]
    D = [tuple(t) for t in (r.get("D_terms") or [])]
    out = dict(r)
    try:
        code = build_pbb_code(r["ell"], r["m"], A, B, C, D)
        h = is_equivalently_css(code)
        out["lc_hadamard"] = bool(h.get("is_css", False))
    except Exception as e:
        out["lc_hadamard"] = None
        out["lc_hadamard_err"] = str(e)
    try:
        g = is_lc_equivalent_css_group(r["ell"], r["m"], A, B, C, D)
        out["lc_uniform"] = bool(g.get("is_lc_css", False))
        if "s1" in g and "s2" in g:
            out["lc_uniform_s1"] = g.get("s1")
            out["lc_uniform_s2"] = g.get("s2")
    except Exception as e:
        out["lc_uniform"] = None
        out["lc_uniform_err"] = str(e)
    try:
        e = verify_uniform_reduction_exact(r["ell"], r["m"], A, B, C, D)
        out["lc_nonuniform_IS_HS"] = bool(e.get("reduction_holds", False))
        out["lc_uniform_solutions"] = e.get("uniform_solutions", [])
    except Exception as ex:
        out["lc_nonuniform_IS_HS"] = None
        out["lc_nonuniform_IS_HS_err"] = str(ex)

    out["lc_any"] = bool(out.get("lc_hadamard")) or bool(out.get("lc_uniform"))
    return out


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("--input", default="results/campaign7_dedup.jsonl",
                    help="JSONL catalog of PBB records to analyze.")
    ap.add_argument("--output", default="results/campaign7_lc_analysis.jsonl",
                    help="JSONL output path for per-record LC results.")
    ap.add_argument("--workers", type=int, default=2)
    args = ap.parse_args()

    base = [json.loads(l) for l in open(args.input) if l.strip()]
    print(f"running LC analysis on {len(base)} records from {args.input}")

    t0 = time.time()
    out_path = Path(args.output)
    completed = 0
    with out_path.open("w") as f, ProcessPoolExecutor(max_workers=args.workers) as pool:
        futs = {pool.submit(lc_worker, json.dumps(r)): r for r in base}
        for fut in as_completed(futs):
            try:
                result = fut.result()
            except Exception as e:
                r = futs[fut]
                result = {**r, "lc_error": str(e)}
            f.write(json.dumps(result) + "\n")
            f.flush()
            completed += 1
            if completed % 25 == 0 or completed == len(base):
                elapsed = time.time() - t0
                print(f"[{completed}/{len(base)}] elapsed {elapsed:.0f}s",
                      flush=True)

    # Summary
    recs = [json.loads(l) for l in out_path.open() if l.strip()]
    n_hadamard = sum(1 for r in recs if r.get("lc_hadamard"))
    n_uniform = sum(1 for r in recs if r.get("lc_uniform"))
    n_nonuniform = sum(1 for r in recs if r.get("lc_nonuniform_IS_HS"))
    n_any = sum(1 for r in recs if r.get("lc_any"))
    print(f"\nLC-CSS analysis on {len(recs)} records:")
    print(f"  Hadamard (parity-2-coloring):                {n_hadamard}")
    print(f"  Uniform per-block S/H:                       {n_uniform}")
    print(f"  Non-uniform {{I,S}}/{{H,HS}} reduction holds:    {n_nonuniform}")
    print(f"  any LC-CSS:                                  {n_any}")
    print(f"  remaining CSS-inequivalent (tested LC):      {len(recs) - n_any}")


if __name__ == "__main__":
    main()
