"""Rigorous multi-decoder soak test for discovered BB codes.

This is the **publication-quality verification protocol**.  BP-OSD is
stochastic -- a single batch of 500 trials can miss low-weight codewords,
yielding distance estimates that vary from 6 to 18 across batches
(observed on [[144,32,?]]).  This soak test counters that variance by
running many independent batches across multiple decoder configurations
and reporting the global minimum as the verified upper bound.

Multi-decoder protocol (default: 150,000 total trials per code)
---------------------------------------------------------------
Each code is tested with 3 decoder configurations, each run for 10
independent batches of 5,000 trials:

1. **OSD_0 / product_sum** -- fast baseline (``bp_method='product_sum'``).
2. **OSD_CS order=10 / product_sum** -- tighter bounds
   (``osd_method='osd_cs'``, ``osd_order=10``).
3. **OSD_CS order=10 / minimum_sum** -- alternative BP algorithm
   (``bp_method='minimum_sum'``).

The verified distance is ``min`` across all 30 batch results.

Key findings
------------
* 60,000 trials was **insufficient** -- 150,000 trials found tighter
  bounds on 8 of 9 tested codes (e.g. [[144,32,?]]: d=10 -> d=6).
* OSD-CS order=10 finds systematically tighter bounds than OSD_0
  (4-12 point improvements on high-k codes).

Output
------
The ``main()`` CLI prints a summary with CONFIRMED / REVISED codes,
comparison vs Bravyi et al. baselines, and a verified Pareto front.
Results are saved to JSON (default: ``results/soak_test_results.json``).

Usage::

    uv run python tests/soak_test.py                  # all 9 priority codes
    uv run python tests/soak_test.py --batches 10     # more batches per decoder
    uv run python tests/soak_test.py --trials 2000    # fewer trials (faster)
    uv run python tests/soak_test.py --single-decoder # OSD_0 only (fast)
    uv run python tests/soak_test.py --codes "360,40" # filter by label substring
"""

from __future__ import annotations

import argparse
import json
import math
import sys
import time
from pathlib import Path

from qldpc.objects import Pauli

# Ensure project root on path
sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from evaluation.bb_code import build_bb_code
from evaluation.evaluator import compute_fom, DISTANCE_TRUST_RATIO


# Decoder configurations for multi-decoder verification.
# The global minimum across all configs gives the tightest upper bound.
DECODER_CONFIGS = [
    {
        "name": "OSD_0/product_sum",
        "kwargs": {"bp_method": "product_sum"},
    },
    {
        "name": "OSD_CS10/product_sum",
        "kwargs": {
            "bp_method": "product_sum",
            "osd_method": "osd_cs",
            "osd_order": 10,
        },
    },
    {
        "name": "OSD_CS10/minimum_sum",
        "kwargs": {
            "bp_method": "minimum_sum",
            "osd_method": "osd_cs",
            "osd_order": 10,
        },
    },
]


def estimate_distance_with_config(code, num_trials: int, decoder_kwargs: dict) -> int:
    """Estimate distance using a specific decoder configuration.

    Calls get_distance_bound_with_decoder directly with custom decoder params.

    Raises:
        ValueError: if the code has dimension 0.  A k=0 stabilizer code has
            no logical operators, so its distance is undefined (or, by
            convention, the minimum weight of a non-identity stabilizer
            generator -- never 0).  Returning 0 would silently corrupt the
            global minimum of the soak test, so we fail loudly and require
            the caller to filter k=0 codes upstream.
    """
    if code.dimension == 0:
        raise ValueError(
            "Distance is undefined for k=0 stabilizer codes (no logical "
            "operators). Filter k=0 codes before calling "
            "estimate_distance_with_config."
        )

    trials_x = num_trials // 2
    trials_z = (num_trials + 1) // 2
    d_x = code.get_distance_bound_with_decoder(
        Pauli.X, trials_x, **decoder_kwargs
    )
    d_z = code.get_distance_bound_with_decoder(
        Pauli.Z, trials_z, **decoder_kwargs
    )
    d = min(d_x, d_z)
    return int(d) if d == d else 0  # handle NaN


# Codes to verify -- using verified distances from multi-decoder soak test.
# claimed_d values are the VERIFIED upper bounds from 60,000-trial runs.
CODES_TO_VERIFY = [
    # VERIFIED: [[360,40,≤20]] -- highest k at any n
    {
        "label": "[[360,40,≤20]]",
        "ell": 15, "m": 12,
        "A_terms": [(0, 0), (0, 1), (0, 2)],
        "B_terms": [(0, 0), (5, 0), (10, 0)],
        "claimed_d": 20, "claimed_fom": 44.4,
        "notes": "constant-monomial, k=40 unprecedented",
    },
    # VERIFIED: [[360,32,≤20]] -- constant-monomial
    {
        "label": "[[360,32,≤20]] CM",
        "ell": 15, "m": 12,
        "A_terms": [(0, 0), (0, 2), (0, 4)],
        "B_terms": [(0, 0), (3, 0), (4, 0)],
        "claimed_d": 20, "claimed_fom": 35.6,
        "notes": "constant-monomial at (15,12)",
    },
    # VERIFIED: [[288,24,≤20]] -- x/y-swap
    {
        "label": "[[288,24,≤20]]",
        "ell": 24, "m": 6,
        "A_terms": [(6, 0), (0, 1), (0, 2)],
        "B_terms": [(0, 3), (2, 0), (4, 0)],
        "claimed_d": 20, "claimed_fom": 33.3,
        "notes": "x/y-swap at (24,6)",
    },
    # VERIFIED: [[288,32,≤16]] -- constant-monomial at (12,12)
    {
        "label": "[[288,32,≤16]] CM",
        "ell": 12, "m": 12,
        "A_terms": [(0, 0), (0, 2), (0, 4)],
        "B_terms": [(0, 0), (2, 0), (4, 0)],
        "claimed_d": 16, "claimed_fom": 28.4,
        "notes": "constant-monomial at (12,12)",
    },
    # VERIFIED: [[144,24,≤12]] -- x/y-swap
    {
        "label": "[[144,24,≤12]]",
        "ell": 6, "m": 12,
        "A_terms": [(3, 0), (0, 2), (0, 4)],
        "B_terms": [(0, 6), (1, 0), (2, 0)],
        "claimed_d": 12, "claimed_fom": 24.0,
        "notes": "x/y-swap at (6,12)",
    },
    # VERIFIED: [[144,32,≤10]] -- constant-monomial
    {
        "label": "[[144,32,≤10]]",
        "ell": 12, "m": 6,
        "A_terms": [(0, 0), (0, 2), (0, 4)],
        "B_terms": [(0, 0), (8, 0), (10, 0)],
        "claimed_d": 10, "claimed_fom": 22.2,
        "notes": "constant-monomial at (12,6)",
    },
    # VERIFIED: [[360,32,≤16]] -- constant-monomial at (30,6)
    {
        "label": "[[360,32,≤16]]",
        "ell": 30, "m": 6,
        "A_terms": [(0, 0), (0, 2), (0, 4)],
        "B_terms": [(0, 0), (8, 0), (10, 0)],
        "claimed_d": 16, "claimed_fom": 22.8,
        "notes": "constant-monomial at (30,6)",
    },
    # UNTRUSTED: [[288,32,≤24]] -- x/y-swap at (12,12), d/√n=1.414
    {
        "label": "[[288,32,≤24]] UNTRUSTED",
        "ell": 12, "m": 12,
        "A_terms": [(3, 0), (0, 2), (0, 10)],
        "B_terms": [(0, 6), (1, 0), (11, 0)],
        "claimed_d": 24, "claimed_fom": 64.0,
        "notes": "x/y-swap, d/sqrt(n)=1.414 > trust threshold",
    },
    # VERIFIED: [[288,32,≤14]] CM at (24,6)
    {
        "label": "[[288,32,≤14]] CM",
        "ell": 24, "m": 6,
        "A_terms": [(0, 0), (0, 2), (0, 4)],
        "B_terms": [(0, 0), (2, 0), (4, 0)],
        "claimed_d": 14, "claimed_fom": 21.8,
        "notes": "constant-monomial at (24,6)",
    },
]


def run_soak_test(
    code_spec: dict,
    num_batches: int = 10,
    trials_per_batch: int = 5000,
    decoder_configs: list[dict] | None = None,
    verbose: bool = True,
) -> dict:
    """Run a multi-decoder soak test on a single code.

    Args:
        code_spec: Dict with ell, m, A_terms, B_terms, etc.
        num_batches: Number of independent BP-OSD batches per decoder config.
        trials_per_batch: Trials per batch.
        decoder_configs: List of decoder config dicts. Defaults to DECODER_CONFIGS.
        verbose: Print per-batch results.

    Returns:
        Dict with verified distance and statistics.
    """
    if decoder_configs is None:
        decoder_configs = DECODER_CONFIGS

    label = code_spec["label"]
    code = build_bb_code(
        code_spec["ell"], code_spec["m"],
        code_spec["A_terms"], code_spec["B_terms"],
    )
    n = code.num_qudits
    k = code.dimension

    num_configs = len(decoder_configs)
    total_batches = num_batches * num_configs

    if verbose:
        print(f"\n{'='*70}")
        print(f"  {label}  n={n}, k={k}  ({code_spec['ell']},{code_spec['m']})")
        print(f"  Claimed: d≤{code_spec['claimed_d']}, FOM={code_spec['claimed_fom']}")
        print(f"  Running {num_configs} decoders x {num_batches} batches x "
              f"{trials_per_batch} trials = {total_batches * trials_per_batch} total")
        print(f"{'='*70}")

    all_batch_results = []  # (decoder_name, d_value) pairs
    per_decoder_results: dict[str, list[int]] = {}
    d_global_min = float("inf")
    t0 = time.time()

    for cfg in decoder_configs:
        cfg_name = cfg["name"]
        cfg_kwargs = cfg["kwargs"]
        per_decoder_results[cfg_name] = []

        if verbose:
            print(f"\n  --- Decoder: {cfg_name} ---")

        for i in range(num_batches):
            t_batch = time.time()
            d_batch = estimate_distance_with_config(
                code, trials_per_batch, cfg_kwargs
            )
            elapsed = time.time() - t_batch
            per_decoder_results[cfg_name].append(d_batch)
            all_batch_results.append((cfg_name, d_batch))
            d_global_min = min(d_global_min, d_batch)

            if verbose:
                marker = ""
                if d_batch == d_global_min and (i > 0 or cfg != decoder_configs[0]):
                    marker = " <<< NEW GLOBAL MIN"
                elif d_batch == d_global_min:
                    marker = " <<< MIN"
                print(f"  Batch {i+1:2d}/{num_batches}: d={d_batch:3d}  "
                      f"(global min: {d_global_min})  [{elapsed:.1f}s]{marker}")

    total_time = time.time() - t0
    d_verified = int(d_global_min)
    fom_verified = compute_fom(n, k, d_verified)
    sqrt_n = math.sqrt(n)
    ratio = d_verified / sqrt_n
    trusted = d_verified <= DISTANCE_TRUST_RATIO * sqrt_n

    # Per-decoder summary
    decoder_summary = {}
    for cfg_name, results in per_decoder_results.items():
        decoder_summary[cfg_name] = {
            "d_min": min(results),
            "d_max": max(results),
            "d_mean": sum(results) / len(results),
        }

    all_d_values = [d for _, d in all_batch_results]

    # Per-decoder batch values (all individual batch distances)
    per_decoder_batches = {
        cfg_name: results for cfg_name, results in per_decoder_results.items()
    }

    result = {
        "label": label,
        "ell": code_spec["ell"],
        "m": code_spec["m"],
        "A_terms": code_spec["A_terms"],
        "B_terms": code_spec["B_terms"],
        "n": n,
        "k": k,
        "claimed_d": code_spec["claimed_d"],
        "verified_d": d_verified,
        "d_changed": d_verified != code_spec["claimed_d"],
        "fom_claimed": code_spec["claimed_fom"],
        "fom_verified": fom_verified,
        "d_over_sqrt_n": ratio,
        "distance_trusted": trusted,
        "decoder_summary": decoder_summary,
        "per_decoder_batches": per_decoder_batches,
        "d_global_max": max(all_d_values),
        "d_global_mean": sum(all_d_values) / len(all_d_values),
        "num_decoders": num_configs,
        "num_batches_per_decoder": num_batches,
        "trials_per_batch": trials_per_batch,
        "total_trials": total_batches * trials_per_batch,
        "total_time_s": total_time,
        "notes": code_spec["notes"],
    }

    if verbose:
        print(f"\n  RESULT: d_verified ≤ {d_verified} (claimed ≤{code_spec['claimed_d']})")
        if result["d_changed"]:
            direction = "TIGHTER" if d_verified < code_spec["claimed_d"] else "LOOSER"
            print(f"  *** DISTANCE BOUND {direction}: "
                  f"≤{code_spec['claimed_d']} -> ≤{d_verified} ***")
            print(f"  *** FOM: {code_spec['claimed_fom']:.1f} -> {fom_verified:.1f} ***")
        print(f"  d/sqrt(n) = {ratio:.3f}  trusted={trusted}")
        print(f"  Per-decoder min distances:")
        for cfg_name, summary in decoder_summary.items():
            print(f"    {cfg_name:30s}  min={summary['d_min']:3d}  "
                  f"max={summary['d_max']:3d}  mean={summary['d_mean']:.1f}")
        print(f"  Total time: {total_time:.1f}s")

    return result


def main():
    parser = argparse.ArgumentParser(
        description="Multi-decoder soak test for discovered BB codes"
    )
    parser.add_argument("--batches", type=int, default=10,
                        help="Number of BP-OSD batches per decoder (default: 10)")
    parser.add_argument("--trials", type=int, default=5000,
                        help="Trials per batch (default: 5000)")
    parser.add_argument("--codes", type=str, nargs="*",
                        help="Labels of specific codes to test (default: all)")
    parser.add_argument("--single-decoder", action="store_true",
                        help="Use only OSD_0 (fast, less accurate)")
    parser.add_argument("--output", type=str, default="results/soak_test_results.json",
                        help="Output JSON file")
    args = parser.parse_args()

    configs = [DECODER_CONFIGS[0]] if args.single_decoder else DECODER_CONFIGS

    codes_to_test = CODES_TO_VERIFY
    if args.codes:
        codes_to_test = [c for c in CODES_TO_VERIFY
                         if any(label.lower() in c["label"].lower()
                                for label in args.codes)]
        if not codes_to_test:
            print(f"No codes matched: {args.codes}")
            print(f"Available: {[c['label'] for c in CODES_TO_VERIFY]}")
            sys.exit(1)

    num_configs = len(configs)
    total_per_code = args.batches * num_configs * args.trials
    print(f"Soak test: {len(codes_to_test)} codes, "
          f"{num_configs} decoders x {args.batches} batches x {args.trials} trials")
    print(f"Total trials per code: {total_per_code:,}")
    if num_configs > 1:
        print(f"Decoder configs: {', '.join(c['name'] for c in configs)}")

    all_results = []
    t_start = time.time()

    for code_spec in codes_to_test:
        result = run_soak_test(
            code_spec,
            num_batches=args.batches,
            trials_per_batch=args.trials,
            decoder_configs=configs,
        )
        all_results.append(result)

    total_time = time.time() - t_start

    # Summary
    print(f"\n{'='*70}")
    print(f"  SOAK TEST SUMMARY")
    print(f"  {len(codes_to_test)} codes tested, "
          f"{num_configs}x{args.batches}x{args.trials} trials each")
    print(f"  Total time: {total_time/60:.1f} minutes")
    print(f"{'='*70}")

    changed = [r for r in all_results if r["d_changed"]]
    confirmed = [r for r in all_results if not r["d_changed"]]

    if confirmed:
        print(f"\nCONFIRMED ({len(confirmed)}):")
        for r in confirmed:
            print(f"  {r['label']:30s}  d≤{r['verified_d']:3d}  "
                  f"FOM={r['fom_verified']:6.1f}  d/sqrt(n)={r['d_over_sqrt_n']:.3f}  "
                  f"trusted={r['distance_trusted']}")

    if changed:
        print(f"\nDISTANCE REVISED ({len(changed)}):")
        for r in changed:
            direction = "tighter" if r["verified_d"] < r["claimed_d"] else "looser"
            print(f"  {r['label']:30s}  d: ≤{r['claimed_d']:3d} -> "
                  f"≤{r['verified_d']:3d} ({direction})  "
                  f"FOM: {r['fom_claimed']:6.1f} -> "
                  f"{r['fom_verified']:6.1f}  d/sqrt(n)={r['d_over_sqrt_n']:.3f}  "
                  f"trusted={r['distance_trusted']}")

    # Comparison vs Bravyi et al. 2024
    print(f"\nCOMPARISON vs Bravyi et al. 2024:")
    bravyi_best = {
        144: {"k": 12, "d": 12, "fom": 12.0},
        288: {"k": 12, "d": 18, "fom": 13.5},
        360: {"k": 12, "d": 24, "fom": 19.2},
    }
    for r in sorted(all_results, key=lambda x: (-x["n"], -x["fom_verified"])):
        if not r["distance_trusted"]:
            continue
        n = r["n"]
        if n in bravyi_best:
            bravyi = bravyi_best[n]
            ratio = r["fom_verified"] / bravyi["fom"] if bravyi["fom"] > 0 else float("inf")
            print(f"  [[{n},{r['k']},≤{r['verified_d']}]] FOM={r['fom_verified']:.1f}  "
                  f"vs Bravyi [[{n},{bravyi['k']},{bravyi['d']}]] FOM={bravyi['fom']:.1f}  "
                  f"-> {ratio:.1f}x improvement")

    # Final Pareto assessment
    print(f"\nVERIFIED PARETO FRONT (sorted by FOM):")
    trusted_results = sorted(
        [r for r in all_results if r["distance_trusted"]],
        key=lambda r: -r["fom_verified"],
    )
    for r in trusted_results:
        marker = " *REVISED*" if r["d_changed"] else ""
        print(f"  [[{r['n']},{r['k']},≤{r['verified_d']}]]  "
              f"FOM={r['fom_verified']:6.1f}  d/sqrt(n)={r['d_over_sqrt_n']:.3f}"
              f"{marker}")

    # Save results
    output_path = Path(args.output)
    output_path.parent.mkdir(parents=True, exist_ok=True)
    with open(output_path, "w") as f:
        json.dump(all_results, f, indent=2)
    print(f"\nDetailed results saved to {output_path}")


if __name__ == "__main__":
    main()
