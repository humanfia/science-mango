"""Verify all codes discovered by ensemble evolution runs.

Replicates the two-round verification protocol used for the Gemini 3 Flash
run, applied to every unique code discovered by the ensemble runs:

* ``run_20260219_203003`` -- 251-iteration ensemble run (early-stopped)
* ``run_20260220_060158`` -- 500-iteration ensemble run (completed)

Codes already verified in ``soak_test_publication.json`` are skipped.

Two-round protocol (matching Gemini 3 Flash methodology)
---------------------------------------------------------
**Round 1 -- 60k trials** (3 decoders x 10 batches x 2,000 trials):
    Initial verification pass.  Provides first tightened bounds.
    Output: ``results/ensemble_verification_60k.json``

**Round 2 -- 150k trials** (3 decoders x 10 batches x 5,000 trials):
    Publication-quality verification.  The definitive upper bounds.
    Output: ``results/ensemble_verification_150k.json``

Comparing the two rounds demonstrates the methodological finding that
60k trials are insufficient for reliable distance bounds (observed in the
Gemini Flash verification: 150k found tighter bounds on 8/9 codes).

Results are saved incrementally (after each code) so runs can be
interrupted and resumed with ``--resume``.

Usage::

    uv run python tests/verify_ensemble_codes.py --round 60k
    uv run python tests/verify_ensemble_codes.py --round 150k
    uv run python tests/verify_ensemble_codes.py --round 60k --resume
"""
from __future__ import annotations

import argparse
import json
import sys
import time
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from tests.soak_test import run_soak_test, DECODER_CONFIGS
from evaluation.evaluator import DISTANCE_TRUST_RATIO


DISCOVERED_CODES_PATH = Path("results/discovered_codes.json")
ALREADY_VERIFIED_PATH = Path("results/soak_test_publication.json")

ROUND_CONFIGS = {
    "60k": {
        "batches": 10,
        "trials": 2000,
        "total_per_code": 60_000,
        "output": Path("results/ensemble_verification_60k.json"),
    },
    "150k": {
        "batches": 10,
        "trials": 5000,
        "total_per_code": 150_000,
        "output": Path("results/ensemble_verification_150k.json"),
    },
}


def _code_signature(entry: dict) -> tuple:
    """Canonical signature for deduplication: (ell, m, sorted A_terms, sorted B_terms)."""
    return (
        entry["ell"],
        entry["m"],
        tuple(sorted(tuple(t) for t in entry["A_terms"])),
        tuple(sorted(tuple(t) for t in entry["B_terms"])),
    )


def load_codes_to_verify() -> list[dict]:
    """Load all unique codes from discovered_codes.json, excluding already-verified ones."""
    with open(DISCOVERED_CODES_PATH) as f:
        discovered = json.load(f)

    # Build set of already-verified signatures
    already_verified = set()
    if ALREADY_VERIFIED_PATH.exists():
        with open(ALREADY_VERIFIED_PATH) as f:
            for entry in json.load(f):
                already_verified.add(_code_signature(entry))

    # Deduplicate: keep entry with highest FOM for each signature
    best_by_sig: dict[tuple, dict] = {}
    for entry in discovered:
        sig = _code_signature(entry)
        if sig in already_verified:
            continue
        if sig not in best_by_sig or entry["fom"] > best_by_sig[sig]["fom"]:
            best_by_sig[sig] = entry

    # Convert to soak test format, sorted by FOM descending (best first)
    codes = []
    for sig, entry in sorted(best_by_sig.items(), key=lambda x: -x[1]["fom"]):
        n = entry["n"]
        k = entry["k"]
        d = entry["d"]
        # Classify pattern
        a_terms = entry["A_terms"]
        b_terms = entry["B_terms"]
        is_cm = all(t[0] == 0 for t in a_terms) and all(t[1] == 0 for t in b_terms)
        pattern = "CM" if is_cm else "swap"

        code_spec = {
            "label": f"[[{n},{k},<={d}]] {pattern} ({entry['ell']},{entry['m']})",
            "ell": entry["ell"],
            "m": entry["m"],
            "A_terms": [tuple(t) for t in a_terms],
            "B_terms": [tuple(t) for t in b_terms],
            "claimed_d": d,
            "claimed_fom": entry["fom"],
            "notes": f"{pattern} at ({entry['ell']},{entry['m']}), evolution d_est={d}",
        }
        codes.append(code_spec)

    return codes


def load_completed_signatures(output_path: Path) -> set[tuple]:
    """Load signatures of codes already completed in a partial output file."""
    if not output_path.exists():
        return set()
    with open(output_path) as f:
        results = json.load(f)
    return {_code_signature(r) for r in results}


def main():
    parser = argparse.ArgumentParser(
        description="Verify all ensemble-discovered codes (two-round protocol)"
    )
    parser.add_argument("--round", type=str, choices=["60k", "150k"], required=True,
                        help="Verification round: '60k' (initial) or '150k' (publication)")
    parser.add_argument("--resume", action="store_true",
                        help="Skip codes already in the output file")
    parser.add_argument("--output", type=str, default=None,
                        help="Override output JSON path")
    parser.add_argument("--codes", type=str, nargs="*",
                        help="Filter by label substring")
    args = parser.parse_args()

    round_cfg = ROUND_CONFIGS[args.round]
    output_path = Path(args.output) if args.output else round_cfg["output"]

    configs = DECODER_CONFIGS
    num_batches = round_cfg["batches"]
    trials_per_batch = round_cfg["trials"]

    # Load codes
    codes = load_codes_to_verify()

    if args.codes:
        codes = [c for c in codes
                 if any(label.lower() in c["label"].lower() for label in args.codes)]
        if not codes:
            print(f"No codes matched filter: {args.codes}")
            sys.exit(1)

    # Resume support: skip already-completed codes
    completed_sigs = set()
    existing_results = []
    if args.resume:
        if output_path.exists():
            with open(output_path) as f:
                existing_results = json.load(f)
            completed_sigs = {_code_signature(r) for r in existing_results}
            print(f"Resuming: {len(completed_sigs)} codes already done")

        remaining = [c for c in codes if _code_signature(c) not in completed_sigs]
        print(f"Remaining: {len(remaining)} of {len(codes)} codes")
        codes = remaining

    if not codes:
        print("All codes already verified!")
        sys.exit(0)

    num_configs = len(configs)
    total_per_code = num_batches * num_configs * trials_per_batch
    # Rough estimate: 150k ~ 5 min/code, 60k ~ 2 min/code on M4 Max
    estimated_time_per_code_min = 5 if args.round == "150k" else 2
    estimated_total_hours = len(codes) * estimated_time_per_code_min / 60

    print(f"\n{'='*70}")
    print(f"  ENSEMBLE CODE VERIFICATION -- Round {args.round}")
    print(f"  {len(codes)} codes to verify")
    print(f"  Protocol: {num_configs} decoders x {num_batches} batches x {trials_per_batch} trials")
    print(f"  = {total_per_code:,} total trials per code")
    print(f"  Estimated time: ~{estimated_total_hours:.1f} hours")
    print(f"  Output: {output_path}")
    print(f"{'='*70}")

    results = list(existing_results)  # Start from existing results if resuming
    t_start = time.time()

    for i, code_spec in enumerate(codes):
        print(f"\n[{i+1}/{len(codes)}] {code_spec['label']}")
        t_code = time.time()

        result = run_soak_test(
            code_spec,
            num_batches=num_batches,
            trials_per_batch=trials_per_batch,
            decoder_configs=configs,
            verbose=True,
        )
        results.append(result)

        # Save incrementally after each code
        output_path.parent.mkdir(parents=True, exist_ok=True)
        with open(output_path, "w") as f:
            json.dump(results, f, indent=2)

        time.time() - t_code
        total_elapsed = time.time() - t_start
        codes_done = i + 1
        codes_remaining = len(codes) - codes_done
        avg_per_code = total_elapsed / codes_done
        eta_min = codes_remaining * avg_per_code / 60

        print(f"  Saved ({codes_done}/{len(codes)} done, "
              f"avg {avg_per_code:.0f}s/code, ETA ~{eta_min:.0f} min)")

    total_time = time.time() - t_start

    # Final summary
    print(f"\n{'='*70}")
    print(f"  VERIFICATION COMPLETE")
    print(f"  {len(codes)} codes verified in {total_time/3600:.1f} hours")
    print(f"{'='*70}")

    # Partition results
    all_verified = results  # includes resumed results
    trusted = [r for r in all_verified if r["distance_trusted"]]
    changed = [r for r in all_verified if r["d_changed"]]
    confirmed = [r for r in all_verified if not r["d_changed"]]

    print(f"\nTotal verified: {len(all_verified)}")
    print(f"  Distance confirmed: {len(confirmed)}")
    print(f"  Distance revised:   {len(changed)}")
    print(f"  Trusted (d/sqrt(n) <= {DISTANCE_TRUST_RATIO}): {len(trusted)}")

    # Best codes by n
    print(f"\nBEST VERIFIED CODES BY n (trusted only):")
    bravyi_best = {
        144: {"k": 12, "d": 12, "fom": 12.0, "label": "[[144,12,12]]"},
        288: {"k": 12, "d": 18, "fom": 13.5, "label": "[[288,12,18]]"},
        360: {"k": 12, "d": 24, "fom": 19.2, "label": "[[360,12,<=24]]"},
    }

    by_n: dict[int, list[dict]] = {}
    for r in trusted:
        by_n.setdefault(r["n"], []).append(r)

    for n in sorted(by_n.keys()):
        entries = sorted(by_n[n], key=lambda r: -r["fom_verified"])
        bravyi = bravyi_best.get(n)
        if bravyi:
            print(f"\n  n={n} (Bravyi baseline: {bravyi['label']} FOM={bravyi['fom']})")
        else:
            print(f"\n  n={n}")
        for r in entries[:5]:  # Top 5 per n
            ratio_str = ""
            if bravyi and bravyi["fom"] > 0:
                ratio = r["fom_verified"] / bravyi["fom"]
                ratio_str = f"  ({ratio:.1f}x Bravyi)"
            changed_str = " *REVISED*" if r["d_changed"] else ""
            print(f"    [[{n},{r['k']},<={r['verified_d']}]] "
                  f"FOM={r['fom_verified']:6.1f}  "
                  f"d/sqrt(n)={r['d_over_sqrt_n']:.3f}"
                  f"{ratio_str}{changed_str}")

    # Full Pareto front
    print(f"\n  VERIFIED PARETO FRONT (all n, sorted by FOM):")
    pareto = sorted(trusted, key=lambda r: -r["fom_verified"])
    for r in pareto[:20]:
        changed_str = " *REVISED*" if r["d_changed"] else ""
        print(f"    [[{r['n']},{r['k']},<={r['verified_d']}]] "
              f"FOM={r['fom_verified']:6.1f}  d/sqrt(n)={r['d_over_sqrt_n']:.3f}"
              f"{changed_str}")

    print(f"\nResults saved to {output_path}")


if __name__ == "__main__":
    main()
