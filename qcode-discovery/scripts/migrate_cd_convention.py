"""One-shot migration: swap C_terms <-> D_terms values in PBB data files.

Before this migration the codebase used the legacy convention where the
``C_terms``/``D_terms`` fields in JSONL/JSON data stored polynomials in the
``[D | C]`` (``ptb_code.py``) order, i.e. the code's ``C_terms`` field held
the paper's D polynomial.  After the rename to ``pbb_code.py`` and the flip
of the hstack to ``[C | D]`` (matching paper Eq. 2), the field values must
be swapped so that ``entry['C_terms']`` now holds the paper's C polynomial.

Run once from the repo root::

    uv run python scripts/migrate_cd_convention.py --dry-run   # preview
    uv run python scripts/migrate_cd_convention.py             # apply

Exit code 0 on success.  After success, the repo's data is consistent with
``build_pbb_code(ell, m, A_terms, B_terms, C_terms=entry['C_terms'],
D_terms=entry['D_terms'])`` producing the paper-convention stabilizer.
"""

from __future__ import annotations

import argparse
import json
import os
import sys
import tempfile
from pathlib import Path


# Nested keys that may carry (C_terms, D_terms) inside a record.  The
# top-level record itself is always inspected.
def _swap_on_dict(obj: dict) -> bool:
    """If ``obj`` has both ``C_terms`` and ``D_terms`` (or ``C`` and ``D``
    alongside ``A``/``B``), swap their values in place.  Returns True if a
    swap occurred.  A dict matches at most one of the two name conventions,
    so this returns True at most once per call.
    """
    if "C_terms" in obj and "D_terms" in obj:
        obj["C_terms"], obj["D_terms"] = obj["D_terms"], obj["C_terms"]
        return True
    if "A" in obj and "B" in obj and "C" in obj and "D" in obj:
        obj["C"], obj["D"] = obj["D"], obj["C"]
        return True
    return False


def _swap_recursive(obj, _seen: set[int] | None = None) -> int:
    """Walk the object tree, swapping once per dict with matching keys.

    Uses an ``id()`` visited set so shared references (rare in parsed JSON
    but possible if the caller pre-constructed the tree) are never swapped
    twice.  Returns the total number of swaps.
    """
    if _seen is None:
        _seen = set()
    count = 0
    if isinstance(obj, dict):
        if id(obj) in _seen:
            return 0
        _seen.add(id(obj))
        if _swap_on_dict(obj):
            count += 1
        for v in obj.values():
            if isinstance(v, (list, dict)):
                count += _swap_recursive(v, _seen)
    elif isinstance(obj, list):
        if id(obj) in _seen:
            return 0
        _seen.add(id(obj))
        for item in obj:
            count += _swap_recursive(item, _seen)
    return count


def migrate_jsonl(path: Path, dry_run: bool) -> int:
    """Migrate a JSONL file; return number of records that had a swap."""
    total = 0
    fd, tmppath = tempfile.mkstemp(dir=str(path.parent), prefix=path.name + ".")
    os.close(fd)
    try:
        with path.open("r", encoding="utf-8") as fin, \
                open(tmppath, "w", encoding="utf-8") as fout:
            for line in fin:
                stripped = line.strip()
                if not stripped:
                    fout.write(line)
                    continue
                record = json.loads(stripped)
                total += _swap_recursive(record)
                fout.write(json.dumps(record) + "\n")
        if not dry_run:
            os.replace(tmppath, path)
        else:
            os.remove(tmppath)
    except BaseException:
        if os.path.exists(tmppath):
            os.remove(tmppath)
        raise
    return total


def migrate_json(path: Path, dry_run: bool) -> int:
    """Migrate a JSON file."""
    with path.open("r", encoding="utf-8") as fin:
        data = json.load(fin)
    total = _swap_recursive(data)
    if total and not dry_run:
        with path.open("w", encoding="utf-8") as fout:
            json.dump(data, fout, indent=2)
    return total


TARGETS = [
    "results/campaign7_publication_merged.jsonl",
    "results/campaign7_dedup.jsonl",
    "results/campaign7_deep_milp.jsonl",
    "results/evolution/all_codes_noncss.jsonl",
    "results/evolution/campaign7/all_codes_noncss.jsonl",
    "results/evolution/campaign7d/all_codes_noncss.jsonl",
    "results/evolution/campaign7e/all_codes_noncss.jsonl",
    "results/ptb_survey_6x3.json",
    "results/ptb_survey_6x6.json",
    "results/ptb_survey_6x6_milp.json",
]


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--dry-run", action="store_true",
                        help="Count swaps without rewriting files.")
    parser.add_argument("--repo-root", default=".",
                        help="Path to repository root (default: cwd).")
    args = parser.parse_args()

    root = Path(args.repo_root).resolve()
    missing = []
    grand_total = 0

    for rel in TARGETS:
        p = root / rel
        if not p.exists():
            missing.append(str(p))
            continue
        if p.suffix == ".jsonl":
            n = migrate_jsonl(p, args.dry_run)
        else:
            n = migrate_json(p, args.dry_run)
        print(f"{'would swap' if args.dry_run else 'swapped'} {n:>6} records in {rel}")
        grand_total += n

    print(f"--- total: {grand_total} record swaps ---")
    if missing:
        print("MISSING (skipped):", *missing, sep="\n  ")
    return 0


if __name__ == "__main__":
    sys.exit(main())
