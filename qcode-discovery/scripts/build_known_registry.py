#!/usr/bin/env python3
"""Build the versioned CSS/PBB known-code registry from pinned source data."""

from __future__ import annotations

import argparse
import hashlib
import json
import sys
from datetime import datetime, timezone
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from evaluation.bb_code import build_bb_code
from evaluation.coset_action_catalog import V2_CATALOG_ID, get_catalog
from evaluation.coset_two_block import (
    ACTION_CATALOG_SHA256,
    ACTION_CATALOG_V2_SHA256,
    CONSTRUCTION_REPRESENTATION_V2,
    build_coset_two_block,
    build_coset_two_block_v2,
)
from evaluation.pbb_code import build_pbb_code
from evaluation.registry import (
    canonical_digest_noncss,
    canonical_json_sha256,
)
from evaluation.structural_dedup import (
    KNOWN_CSS_REFERENCES,
    canonical_digest,
)


def file_sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def flatten_json_lists(value):
    if isinstance(value, list):
        return value
    if isinstance(value, dict):
        rows = []
        for item in value.values():
            if isinstance(item, list):
                rows.extend(item)
        return rows
    return []


def main() -> int:
    project = Path(__file__).resolve().parent.parent
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--css-catalog", type=Path,
        default=project / "results" / "ilp_catalog.json",
    )
    parser.add_argument(
        "--css-verified-catalog", type=Path,
        default=project / "results" / "campaign4_milp_verified.jsonl",
    )
    parser.add_argument(
        "--css-ensemble-catalog", type=Path,
        default=project / "results" / "ensemble_verification_150k.json",
    )
    parser.add_argument(
        "--pbb-catalog", type=Path,
        default=project / "results" / "campaign7_publication_merged.jsonl",
    )
    parser.add_argument(
        "--output", type=Path,
        default=project / "results" / "known_code_registry.json",
    )
    args = parser.parse_args()
    entries = []

    # Published nonnormal-coset two-block code from Aydin--Tamo--Barg.  The
    # frozen action catalog is the reconstruction authority; the paper's
    # reported d=16 is registry metadata only and is never promoted to local
    # exact-distance evidence by the search/certificate pipeline.
    coset_action_id = "coset2bga-l224-m53-s1-degree112-v1"
    coset_left_support = ["L000", "L104", "L207"]
    coset_right_support = ["R000", "R009", "R024"]
    coset_code = build_coset_two_block(
        coset_action_id,
        coset_left_support,
        coset_right_support,
    )
    entries.append({
        "id": "literature-aydin-tamo-barg-224-12-16",
        "family": "css-coset-two-block",
        "code_type": "css",
        "n": int(coset_code.num_qudits),
        "k": int(coset_code.dimension),
        "distance_evidence": {
            "d": 16,
            "status": "published",
            "locally_exact_proven": False,
            "source_file_sha256": (
                "1797447d6bea96ffda61b4ce6a91b560b6d52fe2784983c01df6166c5ed69734"
            ),
        },
        "canonical_digest": canonical_digest(coset_code),
        "construction": {
            "kind": "coset-two-block-v1",
            "action_id": coset_action_id,
            "action_catalog_sha256": ACTION_CATALOG_SHA256,
            "left_support": coset_left_support,
            "right_support": coset_right_support,
        },
        "provenance": [{
            "kind": "literature",
            "source": "Aydin, Tamo, and Barg, Coset Two-Block Group Algebra Codes",
            "arxiv": "2606.17268",
            "reproduction_repository": (
                "https://github.com/aaydinnnn/Coset2BGACodes"
            ),
            "reproduction_commit": (
                "a828dc43c55982e0212febea634775d36bf6e968"
            ),
            "reproduction_file": (
                "code_dict/code_n224_k12_d16_l224_m53_s1_"
                "a1_81_186_b1_16_47.json"
            ),
        }],
    })

    # Register every published 3+3 anchor carried by the source-bound v2
    # catalog.  Without these entries, expanding Stage 1 to the official
    # action catalog could cause Stage 2 to label a reproduced literature
    # construction as novel.  Reported distances remain metadata only; the
    # certificate pipeline must independently prove any distance claim.
    coset_v2_catalog = get_catalog(catalog_id=V2_CATALOG_ID)
    for action in sorted(
        coset_v2_catalog.actions.values(), key=lambda item: item.action_id
    ):
        published = action.published_support
        if published is None:
            continue
        left_support = list(published["left_support"])
        right_support = list(published["right_support"])
        code = build_coset_two_block_v2(
            action.action_id, left_support, right_support,
        )
        reported_n = int(published["reported_n"])
        reported_k = int(published["reported_k"])
        if (
            int(code.num_qudits) != reported_n
            or int(code.dimension) != reported_k
        ):
            raise RuntimeError(
                f"published v2 anchor {action.action_id} does not rebuild "
                "its reported [[n,k]]"
            )
        entries.append({
            "id": f"literature-aydin-tamo-barg-{action.action_id}",
            "family": "css-coset-two-block",
            "code_type": "css",
            "n": reported_n,
            "k": reported_k,
            "distance_evidence": {
                "d": int(published["reported_distance"]),
                "status": str(published["distance_evidence_status"]),
                "reported_exact": bool(published["reported_distance_exact"]),
                "locally_exact_proven": False,
            },
            "canonical_digest": canonical_digest(code),
            "construction": {
                "kind": "coset-two-block-v2",
                "representation_id": CONSTRUCTION_REPRESENTATION_V2,
                "action_id": action.action_id,
                "action_catalog_id": V2_CATALOG_ID,
                "action_catalog_sha256": ACTION_CATALOG_V2_SHA256,
                "left_support": left_support,
                "right_support": right_support,
            },
            "provenance": [
                {
                    "kind": "literature-coset2bga-v2",
                    "source": (
                        "Aydin, Tamo, and Barg, "
                        "Coset Two-Block Group Algebra Codes"
                    ),
                    "arxiv": "2606.17268",
                    "reproduction_repository": (
                        "https://github.com/aaydinnnn/Coset2BGACodes"
                    ),
                    "reproduction_commit": (
                        "a828dc43c55982e0212febea634775d36bf6e968"
                    ),
                    "action_id": action.action_id,
                    "source_bindings": [
                        dict(binding) for binding in action.source_bindings
                    ],
                    "action_scope": action.provenance.get("action_scope"),
                }
            ],
        })

    for name, ell, m, a_terms, b_terms in KNOWN_CSS_REFERENCES:
        code = build_bb_code(ell, m, a_terms, b_terms)
        entries.append({
            "id": "literature-" + name.lower().replace(" ", "-"),
            "family": "css-bb",
            "code_type": "css",
            "n": int(code.num_qudits),
            "k": int(code.dimension),
            "distance_evidence": name,
            "canonical_digest": canonical_digest(code),
            "construction": {
                "ell": ell, "m": m,
                "A_terms": a_terms, "B_terms": b_terms,
            },
            "provenance": [{
                "kind": "literature",
                "source": "Bravyi et al. 2024 / ECZoo QCGA",
            }],
        })

    css_data = json.loads(args.css_catalog.read_text())
    for index, row in enumerate(flatten_json_lists(css_data)):
        a_terms = row.get("A") or row.get("A_terms")
        b_terms = row.get("B") or row.get("B_terms")
        if not a_terms or not b_terms:
            continue
        code = build_bb_code(int(row["ell"]), int(row["m"]), a_terms, b_terms)
        entries.append({
            "id": f"qcode-css-{index:04d}",
            "family": "css-bb",
            "code_type": "css",
            "n": int(code.num_qudits),
            "k": int(code.dimension),
            "distance_evidence": {
                "d": row.get("ilp_d"),
                "status": row.get("status"),
                "label": row.get("label"),
            },
            "canonical_digest": canonical_digest(code),
            "construction": {
                "ell": int(row["ell"]), "m": int(row["m"]),
                "A_terms": a_terms, "B_terms": b_terms,
            },
            "provenance": [{
                "kind": "qcode-discovery-css-catalog",
                "source": args.css_catalog.name,
                "row": index,
            }],
        })

    verified_rows = [
        json.loads(line)
        for line in args.css_verified_catalog.read_text().splitlines()
        if line.strip()
    ]
    for index, row in enumerate(verified_rows):
        a_terms, b_terms = row.get("A_terms"), row.get("B_terms")
        if not a_terms or not b_terms:
            continue
        code = build_bb_code(int(row["ell"]), int(row["m"]), a_terms, b_terms)
        entries.append({
            "id": f"qcode-css-verified-{index:04d}",
            "family": "css-bb",
            "code_type": "css",
            "n": int(code.num_qudits),
            "k": int(code.dimension),
            "distance_evidence": {
                "d": row.get("d"),
                "d_is_exact": row.get("d_is_exact"),
                "distance_trusted": row.get("distance_trusted"),
                "stage": row.get("stage"),
            },
            "canonical_digest": canonical_digest(code),
            "construction": {
                "ell": int(row["ell"]), "m": int(row["m"]),
                "A_terms": a_terms, "B_terms": b_terms,
            },
            "provenance": [{
                "kind": "qcode-discovery-css-milp-verified",
                "source": args.css_verified_catalog.name,
                "row": index,
            }],
        })

    ensemble_rows = json.loads(args.css_ensemble_catalog.read_text())
    for index, row in enumerate(ensemble_rows):
        a_terms, b_terms = row.get("A_terms"), row.get("B_terms")
        if not a_terms or not b_terms:
            continue
        code = build_bb_code(int(row["ell"]), int(row["m"]), a_terms, b_terms)
        entries.append({
            "id": f"qcode-css-ensemble-{index:04d}",
            "family": "css-bb",
            "code_type": "css",
            "n": int(code.num_qudits),
            "k": int(code.dimension),
            "distance_evidence": {
                "d": row.get("verified_d"),
                "distance_trusted": row.get("distance_trusted"),
                "label": row.get("label"),
            },
            "canonical_digest": canonical_digest(code),
            "construction": {
                "ell": int(row["ell"]), "m": int(row["m"]),
                "A_terms": a_terms, "B_terms": b_terms,
            },
            "provenance": [{
                "kind": "qcode-discovery-css-ensemble-verified",
                "source": args.css_ensemble_catalog.name,
                "row": index,
            }],
        })

    pbb_rows = [
        json.loads(line) for line in args.pbb_catalog.read_text().splitlines()
        if line.strip()
    ]
    for index, row in enumerate(pbb_rows):
        names = ("A_terms", "B_terms", "C_terms", "D_terms")
        if not all(row.get(name) for name in names):
            continue
        code = build_pbb_code(
            int(row["ell"]), int(row["m"]),
            *(row[name] for name in names),
        )
        entries.append({
            "id": f"qcode-pbb-{index:04d}",
            "family": "pbb-noncss",
            "code_type": "noncss",
            "n": int(code.num_qudits),
            "k": int(code.dimension),
            "distance_evidence": {
                "d": row.get("d"),
                "d_is_exact": bool(
                    row.get("d_is_exact") or row.get("milp_exact_deep")
                ),
                "method": row.get("d_method"),
                "trust_level": row.get("trust_level"),
            },
            "canonical_digest": canonical_digest_noncss(code),
            "construction": {
                "ell": int(row["ell"]), "m": int(row["m"]),
                **{name: row[name] for name in names},
            },
            "provenance": [{
                "kind": "qcode-discovery-pbb-publication",
                "source": args.pbb_catalog.name,
                "row": index,
                "code_id": row.get("code_id"),
            }],
        })

    deduplicated = {}
    for entry in entries:
        key = (
            entry["code_type"], entry["n"], entry["k"],
            entry["canonical_digest"],
        )
        if key not in deduplicated:
            deduplicated[key] = entry
        else:
            deduplicated[key]["provenance"].extend(entry["provenance"])
    final_entries = sorted(
        deduplicated.values(),
        key=lambda row: (
            row["code_type"], row["n"], row["k"], row["canonical_digest"],
        ),
    )
    registry = {
        "schema_version": 1,
        "registry_version": "2026-08-06.qcode-coset-two-block-v2",
        "generated_at": datetime.now(timezone.utc).isoformat(),
        "equivalence_scope": {
            "css": "colored Tanner generator permutation equivalence",
            "noncss": "tied X/Z-support Tanner generator permutation equivalence",
        },
        "sources": [
            {
                "path": str(args.css_catalog.relative_to(project)),
                "sha256": file_sha256(args.css_catalog),
            },
            {
                "path": str(args.css_verified_catalog.relative_to(project)),
                "sha256": file_sha256(args.css_verified_catalog),
            },
            {
                "path": str(args.css_ensemble_catalog.relative_to(project)),
                "sha256": file_sha256(args.css_ensemble_catalog),
            },
            {
                "path": str(args.pbb_catalog.relative_to(project)),
                "sha256": file_sha256(args.pbb_catalog),
            },
            {
                "source": "Bravyi et al. 2024 / ECZoo QCGA",
                "url": "https://errorcorrectionzoo.org/c/qcga",
            },
            {
                "path": "evaluation/coset_two_block_actions.v1.json",
                "sha256": file_sha256(
                    project / "evaluation" / "coset_two_block_actions.v1.json"
                ),
            },
            {
                "path": "evaluation/coset_two_block_actions.v2.json",
                "sha256": file_sha256(
                    project / "evaluation" / "coset_two_block_actions.v2.json"
                ),
            },
            {
                "source": (
                    "Aydin, Tamo, and Barg, Coset Two-Block Group Algebra Codes"
                ),
                "url": "https://arxiv.org/abs/2606.17268",
                "reproduction_repository": (
                    "https://github.com/aaydinnnn/Coset2BGACodes"
                ),
                "reproduction_commit": (
                    "a828dc43c55982e0212febea634775d36bf6e968"
                ),
            },
        ],
        "summary": {
            "raw_entries": len(entries),
            "deduplicated_entries": len(final_entries),
            "css": sum(row["code_type"] == "css" for row in final_entries),
            "noncss": sum(row["code_type"] == "noncss" for row in final_entries),
        },
        "entries": final_entries,
    }
    registry["registry_sha256"] = canonical_json_sha256(
        registry, omit="registry_sha256",
    )
    args.output.parent.mkdir(parents=True, exist_ok=True)
    temporary = args.output.with_suffix(args.output.suffix + ".tmp")
    temporary.write_text(json.dumps(registry, indent=2) + "\n")
    temporary.replace(args.output)
    print(json.dumps(registry["summary"], indent=2))
    print(f"registry_sha256={registry['registry_sha256']}")
    print(f"output={args.output}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
