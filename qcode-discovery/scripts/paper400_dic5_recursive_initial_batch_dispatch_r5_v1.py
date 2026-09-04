#!/usr/bin/env python3
"""Run the all-sibling initial dispatcher for an r5-adapted bundle."""

from __future__ import annotations

import sys
from collections.abc import Sequence
from pathlib import Path


PROJECT = Path(__file__).resolve().parent.parent
if str(PROJECT) not in sys.path:
    sys.path.insert(0, str(PROJECT))

from scripts import paper400_dic5_recursive_initial_batch_dispatch_v1 as dispatch
from scripts import paper400_dic5_recursive_r5_legacy_adapter_v1 as adapter


def main(argv: Sequence[str] | None = None) -> int:
    with adapter.r5_legacy_context():
        return dispatch.main(list(argv) if argv is not None else None)


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except Exception as exc:  # The frozen dispatcher exposes several error classes.
        print(f"ERROR: {exc}", file=sys.stderr)
        raise SystemExit(2)
