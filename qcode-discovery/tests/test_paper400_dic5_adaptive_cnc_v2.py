from __future__ import annotations

import copy
import hashlib
import inspect
from itertools import product

import pytest

from investigations import paper400_dic5_adaptive_cnc_v2 as adaptive


def _empty_cnf(variables: int) -> bytes:
    return f"p cnf {variables} 0\n".encode("ascii")


def _variable_depth_manifest() -> dict:
    return adaptive.build_adaptive_manifest(
        _empty_cnf(3),
        parent_cube=(),
        candidate_variables=(3, 2, 1),
        status_by_path={
            "R": "UNKNOWN",
            "R+": "UNSAT",
            "R-": "TIMEOUT",
            "R-+": "SAT",
            "R--": "UNKNOWN",
        },
        max_depth=2,
    )


def _reseal_tree_and_manifest(changed: dict) -> dict:
    tree = changed["tree"]
    tree["node_sha256_sequence_sha256"] = adaptive.canonical_sha256([
        node["node_sha256"] for node in tree["nodes"]
    ])
    tree["cover_sha256_sequence_sha256"] = adaptive.canonical_sha256([
        cover["cover_sha256"] for cover in tree["local_covers"]
    ])
    changed["tree"] = adaptive.seal(tree, "tree_sha256")
    return adaptive.seal(changed, "manifest_sha256")


def _resealed_node_attack(manifest: dict, path: str, kind: str) -> dict:
    changed = copy.deepcopy(manifest)
    for index, node in enumerate(changed["tree"]["nodes"]):
        if node["path"] != path:
            continue
        if kind == "edge":
            node["edge_literal"] = -node["edge_literal"]
        elif kind == "assumptions":
            node["assumptions"][-1] = -node["assumptions"][-1]
        elif kind == "bcp-assignment-tuple":
            node["bcp"]["assignment"] = tuple(node["bcp"]["assignment"])
            node["bcp"] = adaptive.seal(node["bcp"], "bcp_sha256")
        else:
            raise AssertionError(kind)
        changed["tree"]["nodes"][index] = adaptive.seal(node, "node_sha256")
        return _reseal_tree_and_manifest(changed)
    raise AssertionError(path)


def _resealed_cover_attack(manifest: dict) -> dict:
    changed = copy.deepcopy(manifest)
    cover = changed["tree"]["local_covers"][0]
    cover["positive_child"]["decision_literal"] *= -1
    changed["tree"]["local_covers"][0] = adaptive.seal(
        cover, "cover_sha256"
    )
    return _reseal_tree_and_manifest(changed)


def test_strict_dimacs_parser_rejects_malformed_inputs() -> None:
    parsed = adaptive.parse_dimacs(
        b"c strict toy\np cnf 3 2\n1 -2\n3 0\n-1 0\n"
    )
    assert parsed["clauses"] == [[1, -2, 3], [-1]]
    for malformed in (
        b"p cnf 2 2\n1 0\n",
        b"p cnf 2 1\n3 0\n",
        b"p cnf 2 1\n1\n",
        b"1 0\np cnf 1 1\n",
        b"p cnf 1 0\n\xff",
    ):
        with pytest.raises(adaptive.AdaptiveCubeError):
            adaptive.parse_dimacs(malformed)


def test_deterministic_bcp_binds_source_and_propagates_to_conflict() -> None:
    cnf = b"p cnf 3 4\n1 0\n-1 2 0\n-2 3 0\n-3 0\n"
    parsed = adaptive.parse_dimacs(cnf)
    first = adaptive.deterministic_bcp(cnf, ())
    assert first == adaptive.deterministic_bcp(cnf, ())
    assert first["source_cnf_sha256"] == hashlib.sha256(cnf).hexdigest()
    assert first["clauses_sha256"] == parsed["clauses_sha256"]
    assert first["propagated_literals"] == [1, 2, 3]
    assert first["conflict"] is True
    assert first["conflict_clause_index"] == 3

    manifest = adaptive.build_adaptive_manifest(
        cnf,
        parent_cube=(),
        candidate_variables=(1, 2, 3),
        status_by_path={},
        max_depth=3,
    )
    root = manifest["tree"]["nodes"][0]
    assert root["observed_status"] == adaptive.BCP_CONFLICT_STATUS
    assert root["terminal_reason"] == "BCP_CONFLICT"


def test_two_polarity_gain_score_and_tie_break_are_exact() -> None:
    cnf = (
        b"p cnf 7 4\n"
        b"-1 3 0\n"
        b"-1 4 0\n"
        b"1 5 0\n"
        b"-2 3 0\n"
    )
    ranking = adaptive.score_candidates(cnf, (), (7, 2, 6, 1))
    assert [record["dimacs_variable"] for record in ranking] == [1, 2, 6, 7]
    assert ranking[0]["left_gain"] == 3
    assert ranking[0]["right_gain"] == 2
    assert ranking[0]["score"] == 3 * 2 + 3 + 2
    assert ranking[1]["score"] == 2 * 1 + 2 + 1
    assert ranking[2]["score"] == ranking[3]["score"] == 3
    assert ranking[2]["dimacs_variable"] < ranking[3]["dimacs_variable"]


def test_conflicting_polarity_has_priority_over_larger_nonconflict_score() -> None:
    cnf = (
        b"p cnf 7 6\n"
        b"1 7 0\n"
        b"1 -7 0\n"
        b"-2 3 0\n"
        b"-2 4 0\n"
        b"2 5 0\n"
        b"2 6 0\n"
    )
    ranking = adaptive.score_candidates(cnf, (), (2, 1))
    assert [record["dimacs_variable"] for record in ranking] == [1, 2]
    assert ranking[0]["conflict_branch_count"] == 1
    assert ranking[1]["conflict_branch_count"] == 0
    assert ranking[0]["score"] < ranking[1]["score"]


@pytest.mark.parametrize("status", ["SAT", "UNSAT"])
def test_non_hard_leaf_is_never_resplit(status: str) -> None:
    manifest = adaptive.build_adaptive_manifest(
        _empty_cnf(2),
        parent_cube=(),
        candidate_variables=(1, 2),
        status_by_path={"R": status},
        max_depth=2,
    )
    root = manifest["tree"]["nodes"][0]
    assert root["candidate_ranking"] == []
    assert root["selected_variable"] is None
    assert root["terminal_reason"] == "NON_HARD_STATUS"


def test_missing_generated_child_statuses_become_pending_frontier() -> None:
    manifest = adaptive.build_adaptive_manifest(
        _empty_cnf(2),
        parent_cube=(),
        candidate_variables=(2, 1),
        status_by_path={"R": "TIMEOUT"},
        max_depth=1,
    )
    by_path = {node["path"]: node for node in manifest["tree"]["nodes"]}
    assert set(by_path) == {"R", "R+", "R-"}
    assert by_path["R"]["terminal_reason"] is None
    for path in ("R+", "R-"):
        assert by_path[path]["observed_status"] == adaptive.PENDING_STATUS
        assert by_path[path]["status_source"] == "generated-frontier-v1"
        assert by_path[path]["terminal_reason"] == "PENDING"
        assert by_path[path]["selected_variable"] is None


def test_missing_nonconflict_root_status_fails_closed() -> None:
    with pytest.raises(adaptive.AdaptiveCubeError, match="root path R"):
        adaptive.build_adaptive_manifest(
            _empty_cnf(2),
            parent_cube=(),
            candidate_variables=(1, 2),
            status_by_path={},
            max_depth=1,
        )


def test_max_nodes_stops_without_creating_half_a_binary_split() -> None:
    manifest = adaptive.build_adaptive_manifest(
        _empty_cnf(4),
        parent_cube=(),
        candidate_variables=(1, 2, 3, 4),
        status_by_path={"R": "TIMEOUT", "R+": "UNKNOWN"},
        max_depth=3,
        max_nodes=3,
    )
    by_path = {node["path"]: node for node in manifest["tree"]["nodes"]}
    assert set(by_path) == {"R", "R+", "R-"}
    assert by_path["R"]["terminal_reason"] is None
    assert by_path["R+"]["terminal_reason"] == "MAX_NODES"
    assert by_path["R-"]["terminal_reason"] == "PENDING"
    assert manifest["coverage"]["mutually_exclusive"] is True
    assert manifest["coverage"]["exhaustive"] is True
    for invalid in (False, 0, adaptive.MAX_NODE_BUDGET + 1):
        with pytest.raises(adaptive.AdaptiveCubeError, match="max_nodes"):
            adaptive.build_adaptive_manifest(
                _empty_cnf(2),
                parent_cube=(),
                candidate_variables=(1, 2),
                status_by_path={"R": "UNSAT"},
                max_depth=1,
                max_nodes=invalid,
            )


def test_variable_depth_tree_is_mutually_exclusive_and_exhaustive() -> None:
    manifest = _variable_depth_manifest()
    nodes = manifest["tree"]["nodes"]
    by_path = {node["path"]: node for node in nodes}
    assert by_path["R"]["selected_variable"] == 1
    assert by_path["R-"]["selected_variable"] == 2
    assert by_path["R+"]["terminal_reason"] == "NON_HARD_STATUS"
    assert by_path["R--"]["terminal_reason"] == "MAX_DEPTH"
    assert set(by_path) == {"R", "R+", "R-", "R-+", "R--"}

    leaves = [node for node in nodes if node["terminal_reason"] is not None]
    assert [leaf["assumptions"] for leaf in leaves] == [[1], [-1, 2], [-1, -2]]
    for values in product((0, 1), repeat=3):
        assignment = {variable: bool(values[variable - 1]) for variable in range(1, 4)}
        matching = [
            leaf for leaf in leaves
            if all(
                assignment[abs(literal)] == (literal > 0)
                for literal in leaf["assumptions"]
            )
        ]
        assert len(matching) == 1
    assert manifest["coverage"]["variable_depth"] is True
    assert manifest["coverage"]["internal_node_count"] == 2
    assert manifest["coverage"]["terminal_leaf_count"] == 3


def test_independent_tree_replay_does_not_call_builder() -> None:
    manifest = _variable_depth_manifest()
    source = inspect.getsource(adaptive.replay_tree_cover)
    assert "build_adaptive_manifest" not in source
    replay = adaptive.replay_tree_cover(manifest, _empty_cnf(3))
    assert replay["valid"] is True
    assert replay["mutually_exclusive"] is True
    assert replay["exhaustive"] is True
    assert adaptive.selfhash_valid(replay, "record_sha256")


def test_test_only_authority_and_external_pin_semantics_are_explicit() -> None:
    manifest = _variable_depth_manifest()
    assert manifest["authority"] == adaptive.AUTHORITY_TEST_ONLY
    assert manifest["test_only"] is True
    assert manifest["production_eligible"] is False
    assert manifest["launch_authorized"] is False

    unpinned = adaptive.verify_adaptive_manifest(manifest, _empty_cnf(3))
    assert unpinned["valid"] is True
    assert unpinned["authenticated"] is False
    assert unpinned["launch_authorized"] is False
    pinned = adaptive.verify_adaptive_manifest(
        manifest,
        _empty_cnf(3),
        expected_manifest_sha256=manifest["manifest_sha256"],
    )
    assert pinned["valid"] is True
    assert pinned["authenticated"] is True
    assert pinned["production_eligible"] is False
    assert pinned["launch_authorized"] is False
    with pytest.raises(adaptive.AdaptiveCubeError, match="pinned SHA-256"):
        adaptive.verify_adaptive_manifest(
            manifest,
            _empty_cnf(3),
            expected_manifest_sha256="0" * 64,
        )


def test_unresealed_hash_tamper_and_wrong_source_are_rejected() -> None:
    manifest = _variable_depth_manifest()
    broken = copy.deepcopy(manifest)
    broken["tree"]["nodes"][0]["augmented_cnf_sha256"] = "0" * 64
    with pytest.raises(adaptive.AdaptiveCubeError, match="self-hash"):
        adaptive.verify_adaptive_manifest(broken, _empty_cnf(3))
    with pytest.raises(adaptive.AdaptiveCubeError, match="source CNF binding"):
        adaptive.verify_adaptive_manifest(
            manifest, b"c changed\np cnf 3 0\n"
        )


@pytest.mark.parametrize("attack", ["edge", "assumptions"])
def test_resealed_node_edge_and_assumption_attacks_are_rejected(attack: str) -> None:
    changed = _resealed_node_attack(_variable_depth_manifest(), "R+", attack)
    assert adaptive.selfhash_valid(changed, "manifest_sha256")
    with pytest.raises(adaptive.AdaptiveCubeError):
        adaptive.verify_adaptive_manifest(changed, _empty_cnf(3))


def test_resealed_local_cover_and_top_coverage_attacks_are_rejected() -> None:
    cover_attack = _resealed_cover_attack(_variable_depth_manifest())
    assert adaptive.selfhash_valid(cover_attack, "manifest_sha256")
    with pytest.raises(adaptive.AdaptiveCubeError, match="local covers"):
        adaptive.verify_adaptive_manifest(cover_attack, _empty_cnf(3))

    coverage_attack = copy.deepcopy(_variable_depth_manifest())
    coverage_attack["coverage"]["terminal_leaf_count"] += 1
    coverage_attack = adaptive.seal(coverage_attack, "manifest_sha256")
    assert adaptive.selfhash_valid(coverage_attack, "manifest_sha256")
    with pytest.raises(adaptive.AdaptiveCubeError, match="coverage"):
        adaptive.verify_adaptive_manifest(coverage_attack, _empty_cnf(3))


def test_recursive_json_types_and_canonical_hash_exceptions_fail_closed() -> None:
    tuple_attack = _resealed_node_attack(
        _variable_depth_manifest(), "R+", "bcp-assignment-tuple"
    )
    assert adaptive.selfhash_valid(tuple_attack, "manifest_sha256")
    with pytest.raises(adaptive.AdaptiveCubeError, match="BCP differs"):
        adaptive.verify_adaptive_manifest(tuple_attack, _empty_cnf(3))

    cyclic = copy.deepcopy(_variable_depth_manifest())
    cyclic["claim_scope"] = cyclic
    assert adaptive.selfhash_valid(cyclic, "manifest_sha256") is False
    with pytest.raises(adaptive.AdaptiveCubeError, match="self-hash"):
        adaptive.verify_adaptive_manifest(cyclic, _empty_cnf(3))
