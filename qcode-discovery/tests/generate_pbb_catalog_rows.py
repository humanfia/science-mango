#!/usr/bin/env python3
"""Generate LaTeX catalog tables for non-CSS PBB codes from campaign7_publication_merged.jsonl."""

from __future__ import annotations

import json
import sys
from collections import defaultdict
from pathlib import Path


def terms_to_poly(terms: list[list[int]], var_x="x", var_y="y") -> str:
    """Convert [(x_exp, y_exp), ...] to LaTeX polynomial string."""
    if not terms:
        return "0"
    monomials = []
    for x_exp, y_exp in sorted(terms):
        parts = []
        if x_exp == 0 and y_exp == 0:
            parts.append("1")
        else:
            if x_exp == 1:
                parts.append(var_x)
            elif x_exp > 1:
                parts.append(f"{var_x}^{{{x_exp}}}")
            if y_exp == 1:
                parts.append(var_y)
            elif y_exp > 1:
                parts.append(f"{var_y}^{{{y_exp}}}")
        monomials.append("".join(parts) if parts else "1")
    return "{+}".join(monomials)


def catalog_distance(code: dict) -> int:
    """Return the strongest retained distance upper bound for a catalog row."""
    return int(code.get("d_deep_milp", code["d"]))


def catalog_fom(code: dict) -> float:
    """Compute FOM from the retained publication distance."""
    d = catalog_distance(code)
    return code["k"] * d * d / code["n"]


def catalog_trust(code: dict) -> str:
    """Return trust level, promoting rows made exact by deep MILP."""
    if code.get("d_is_exact") or code.get("milp_exact") or code.get("milp_exact_deep"):
        return "EXACT"
    return code.get("trust_level", "?")


def assign_class_labels(codes_by_n: dict) -> dict:
    """Assign alphabetical class labels per n based on BLISS hash."""
    labels = {}
    for n, codes in codes_by_n.items():
        # Collect unique hashes, ordered by best FOM descending
        hash_best_fom = {}
        for c in codes:
            h = c["bliss_hash"]
            fom = catalog_fom(c)
            if h not in hash_best_fom or fom > hash_best_fom[h]:
                hash_best_fom[h] = fom
        sorted_hashes = sorted(hash_best_fom, key=lambda h: -hash_best_fom[h])
        for i, h in enumerate(sorted_hashes):
            labels[(n, h)] = str(i + 1)
    return labels


def generate_table(
    n: int,
    codes: list[dict],
    labels: dict,
    *,
    part: int | None = None,
    total_parts: int | None = None,
    rank_start: int = 1,
    total_codes: int | None = None,
    total_distinct: int | None = None,
) -> str:
    """Generate a LaTeX table for all codes at block length n."""
    # Sort by FOM descending, then k descending
    codes_sorted = sorted(codes, key=lambda c: (-catalog_fom(c), -c["k"], c["bliss_hash"]))

    if total_codes is None:
        total_codes = len(codes)
    if total_distinct is None:
        total_distinct = len(set(c["bliss_hash"] for c in codes))

    lines = []
    lines.append(r"\begin{table*}[t]")
    lines.append(r"\centering")

    if part is None:
        caption_head = (
            f"All verified non-CSS PBB codes at $n = {n}$ "
            f"({total_codes} codes, {total_distinct} distinct), "
            f"sorted by $\\FOM = kd^2/n$ descending."
        )
    elif part == 1:
        rank_end = rank_start + len(codes_sorted) - 1
        caption_head = (
            f"All verified non-CSS PBB codes at $n = {n}$ "
            f"({total_codes} codes, {total_distinct} distinct), "
            f"sorted by $\\FOM = kd^2/n$ descending. Part 1 of {total_parts} "
            f"(codes ranked {rank_start}--{rank_end} by FOM; continued in "
            f"Table~\\ref{{tab:pbb_cat{n}_b}})."
        )
    else:
        rank_end = rank_start + len(codes_sorted) - 1
        caption_head = (
            f"All verified non-CSS PBB codes at $n = {n}$ "
            f"(continued from Table~\\ref{{tab:pbb_cat{n}}}; codes ranked "
            f"{rank_start}--{rank_end} by FOM)."
        )

    caption = (
        f"{caption_head}\n"
        f"$d$: MILP distance; $\\leq$ indicates an incumbent upper bound "
        f"(otherwise distances are exact, with all logicals proven optimal)."
    )
    lines.append(f"\\caption{{{caption}}}")
    suffix = "_b" if part and part > 1 else ""
    lines.append(f"\\label{{tab:pbb_cat{n}{suffix}}}")

    # Use tiny for large tables
    if len(codes) > 30:
        lines.append(r"\tiny")
        lines.append(r"\renewcommand{\arraystretch}{0.82}")
        lines.append(r"\setlength{\tabcolsep}{1.5pt}")
    else:
        lines.append(r"\scriptsize")
        lines.append(r"\setlength{\tabcolsep}{2pt}")

    lines.append(
        r"\begin{tabular*}{\textwidth}{@{\extracolsep{\fill}}cllllllcc}"
    )
    lines.append(r"\toprule")
    lines.append(
        r"Cl.\ & $(\ell,m)$ & $A(x,y)$ & $B(x,y)$ & $C(x,y)$ & $D(x,y)$ "
        r"& $k$ & $d$ & $\FOM$ \\"
    )
    lines.append(r"\midrule")

    for c in codes_sorted:
        cl = labels[(n, c["bliss_hash"])]
        lm = f"$({c['ell']},{c['m']})$"
        a_poly = f"${terms_to_poly(c['A_terms'])}$"
        b_poly = f"${terms_to_poly(c['B_terms'])}$"
        c_poly = f"${terms_to_poly(c['C_terms'])}$"
        d_poly = f"${terms_to_poly(c['D_terms'])}$"
        k = c["k"]
        d_val = catalog_distance(c)
        fom = catalog_fom(c)
        trust = catalog_trust(c)

        # Format d with ≤ for TRUSTED / PARTIAL (both are upper bounds)
        if trust in ("TRUSTED", "PARTIAL"):
            d_str = f"$\\leq${d_val}"
            fom_str = f"$\\leq${fom:.1f}"
        else:
            d_str = str(d_val)
            fom_str = f"{fom:.1f}"

        row = (
            f"{cl} & {lm} & {a_poly} & {b_poly} & {c_poly} & {d_poly} "
            f"& {k} & {d_str} & {fom_str} \\\\"
        )
        lines.append(row)

    lines.append(r"\bottomrule")
    lines.append(r"\end{tabular*}")
    lines.append(r"\end{table*}")
    lines.append("")

    return "\n".join(lines)


def main():
    data_file = Path("results/campaign7_publication_merged.jsonl")
    if not data_file.exists():
        print(f"Error: {data_file} not found", file=sys.stderr)
        sys.exit(1)

    all_codes = [json.loads(line) for line in data_file.read_text().strip().split("\n")]

    # Group by n
    codes_by_n = defaultdict(list)
    for c in all_codes:
        codes_by_n[c["n"]].append(c)

    # Assign class labels
    labels = assign_class_labels(codes_by_n)

    # Generate tables
    for n in sorted(codes_by_n):
        codes = sorted(
            codes_by_n[n],
            key=lambda c: (-catalog_fom(c), -c["k"], c["bliss_hash"]),
        )
        total_distinct = len(set(c["bliss_hash"] for c in codes))
        if n == 108:
            split = (len(codes) + 1) // 2
            print(
                generate_table(
                    n,
                    codes[:split],
                    labels,
                    part=1,
                    total_parts=2,
                    rank_start=1,
                    total_codes=len(codes),
                    total_distinct=total_distinct,
                )
            )
            print(
                generate_table(
                    n,
                    codes[split:],
                    labels,
                    part=2,
                    total_parts=2,
                    rank_start=split + 1,
                    total_codes=len(codes),
                    total_distinct=total_distinct,
                )
            )
        else:
            table = generate_table(
                n,
                codes,
                labels,
                total_codes=len(codes),
                total_distinct=total_distinct,
            )
            print(table)

    # Summary
    print(f"% Total: {len(all_codes)} codes across {len(codes_by_n)} block lengths", file=sys.stderr)
    for n in sorted(codes_by_n):
        num_distinct = len(set(c["bliss_hash"] for c in codes_by_n[n]))
        print(f"%   n={n}: {len(codes_by_n[n])} codes, {num_distinct} distinct", file=sys.stderr)


if __name__ == "__main__":
    main()
