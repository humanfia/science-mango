"""Run publication-quality verification on a JSONL list of PBB codes.

Reads each record's `(ell, m, A_terms, B_terms, C_terms, D_terms)`,
runs the 3-stage verification pipeline from
`scripts.verify_publication.publication_verify_worker` (Stage 1
hash-based exact check, Stage 2 MILP with tiered budgets, Stage 3
BP-OSD with five seeds), and streams JSONL output.

Resumable: records already present in the output file (matched by
`(ell, m, A_terms, B_terms, C_terms, D_terms)`) are skipped on
restart, so an interrupted run can be resumed safely.

Use this when you want to re-verify a curated subset of codes (for
example, a deduplicated catalog or a list of newly-discovered codes)
without rerunning the full pipeline in `verify_publication.py`.

Example:
    uv run python scripts/reverify_pbb_jsonl.py \\
        --input results/campaign7_dedup.jsonl \\
        --output results/campaign7_publication_merged.jsonl \\
        --workers 8
"""
import argparse
import json
import os
import sys
import time
from concurrent.futures import ProcessPoolExecutor, as_completed
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from scripts.verify_publication import publication_verify_worker


def key(r):
    return (r["ell"], r["m"],
            tuple(sorted(tuple(t) for t in r["A_terms"])),
            tuple(sorted(tuple(t) for t in r["B_terms"])),
            tuple(sorted(tuple(t) for t in (r.get("C_terms") or []))),
            tuple(sorted(tuple(t) for t in (r.get("D_terms") or []))))


def task_for(r, code_id):
    return (r["ell"], r["m"],
            [tuple(t) for t in r["A_terms"]],
            [tuple(t) for t in r["B_terms"]],
            [tuple(t) for t in (r.get("C_terms") or [])],
            [tuple(t) for t in (r.get("D_terms") or [])],
            r.get("bliss_hash", f"verify_{code_id}"),
            f"verify_{code_id}")


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("--input", required=True,
                    help="JSONL file of PBB code records to verify.")
    ap.add_argument("--output", required=True,
                    help="JSONL file to stream verification results to "
                         "(appended; resumable).")
    ap.add_argument("--workers", type=int, default=8)
    ap.add_argument("--limit", type=int, default=None,
                    help="Only run this many records (for smoke testing)")
    ap.add_argument("--by-n", type=int, default=None,
                    help="Only run records with this n value")
    args = ap.parse_args()

    remaining = [json.loads(l) for l in open(args.input) if l.strip()]
    if args.by_n is not None:
        remaining = [r for r in remaining if 2 * r["ell"] * r["m"] == args.by_n]
    remaining.sort(key=lambda r: (2 * r["ell"] * r["m"], r["ell"], r["m"]))

    done_keys = set()
    if os.path.exists(args.output):
        for line in open(args.output):
            line = line.strip()
            if not line:
                continue
            try:
                r = json.loads(line)
            except Exception:
                continue
            done_keys.add(key(r))
        print(f"resuming: {len(done_keys)} records already in {args.output}")

    pending = [r for r in remaining if key(r) not in done_keys]
    if args.limit is not None:
        pending = pending[: args.limit]
    print(f"verifying {len(pending)} records (out of {len(remaining)} input)")

    if not pending:
        print("nothing to do")
        return

    tasks = [task_for(r, i) for i, r in enumerate(pending)]

    t_start = time.time()
    completed = 0
    with open(args.output, "a") as f, \
            ProcessPoolExecutor(max_workers=args.workers) as pool:
        futs = {pool.submit(publication_verify_worker, t): t for t in tasks}
        for fut in as_completed(futs):
            try:
                result = fut.result()
            except Exception as e:
                t = futs[fut]
                result = {"ell": t[0], "m": t[1], "error": str(e),
                          "A_terms": t[2], "B_terms": t[3],
                          "C_terms": t[4], "D_terms": t[5]}
            f.write(json.dumps(result) + "\n")
            f.flush()
            completed += 1
            elapsed = time.time() - t_start
            n = result.get("n", 2 * result.get("ell", 0) * result.get("m", 0))
            print(
                f"[{completed}/{len(tasks)}] n={n} k={result.get('k')} "
                f"d={result.get('d')} method={result.get('d_method')} "
                f"trust={result.get('trust_level')} "
                f"time={result.get('time_s')}s "
                f"(elapsed {elapsed:.0f}s)",
                flush=True)


if __name__ == "__main__":
    main()
