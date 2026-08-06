"""Stable batch-level MAP descriptor contracts for the typed coset DSL."""

from __future__ import annotations

import copy
import json
from math import comb, gcd
from types import SimpleNamespace

from evolve import coset_policy_dsl as dsl
from evolve import run_evolution as launcher
from openevolve.database import Program
from evolve.coset_search_contract import (
    COSET_BATCH_ORBIT_PROFILE_METRIC,
    COSET_FEATURE_BINS,
    COSET_FEATURE_DIMENSIONS,
    COSET_MAP_SCHEMA_METRIC,
    COSET_MAP_SCHEMA_VERSION,
    COSET_NONNORMAL_LANE_METRIC,
    COSET_NORMAL_LANE_METRIC,
    COSET_PROOF_LADDER_SCHEMA_VERSION,
    COSET_PROOF_LADDER_VERSION_METRIC,
    action_search_view,
    action_search_views,
    canonical_json_sha256,
    coset_batch_map_descriptor,
)


def _descriptor(policy):
    return coset_batch_map_descriptor(
        dsl.render_candidates(policy),
        policy_sha256=dsl.policy_digest(policy),
    )


def _lane(descriptor, *, normal: bool):
    return next(
        lane
        for lane in descriptor["lanes"]
        if lane["subgroup_normal"] is normal
    )


def _normality_class(descriptor, *, normal: bool):
    return next(
        item
        for item in descriptor["classes"]
        if item["subgroup_normal"] is normal
    )


def _mutated_policy(
    *,
    normal: bool,
    offset_delta: int = 0,
    change_stride: bool = False,
    add_support: bool = False,
):
    document = dsl.policy_document(dsl.default_policy())
    action = next(
        item
        for item in document["actions"]
        if action_search_view(item["action_id"]).subgroup_normal is normal
    )
    view = action_search_view(action["action_id"])
    left_count = len(view.left_element_ids) - 1
    right_count = len(view.right_element_ids) - 1
    pair_space = comb(left_count, 2) * comb(right_count, 2)
    if offset_delta:
        action["walk"]["offset"] = (
            action["walk"]["offset"] + offset_delta
        ) % pair_space
    if change_stride:
        stride = action["walk"]["stride"]
        for delta in range(1, pair_space):
            candidate = (stride + delta) % pair_space
            if candidate and gcd(candidate, pair_space) == 1:
                action["walk"]["stride"] = candidate
                break
        assert action["walk"]["stride"] != stride
    if add_support:
        # Find a declaration accepted by the production parser and not equal
        # to the immutable published anchor.  Trying a bounded deterministic
        # prefix keeps the test independent of GAP/catalog enumeration names.
        for left_second in range(1, min(left_count, 12)):
            for right_second in range(1, min(right_count, 12)):
                trial = copy.deepcopy(document)
                trial_action = next(
                    item
                    for item in trial["actions"]
                    if item["action_id"] == action["action_id"]
                )
                trial_action["supports"] = [{
                    "left": [0, left_second],
                    "right": [0, right_second],
                }]
                try:
                    return dsl.parse_policy(json.dumps(trial))
                except dsl.CosetPolicyError:
                    continue
        raise AssertionError("could not construct an explicit support mutation")
    return dsl.parse_policy(json.dumps(document))


def test_descriptor_v3_aggregates_46_lanes_into_two_class_coordinates():
    policy = dsl.default_policy()
    first = _descriptor(policy)
    second = _descriptor(policy)

    assert COSET_MAP_SCHEMA_VERSION == 3
    assert COSET_FEATURE_DIMENSIONS == (
        COSET_NONNORMAL_LANE_METRIC,
        COSET_NORMAL_LANE_METRIC,
        COSET_BATCH_ORBIT_PROFILE_METRIC,
    )
    assert COSET_FEATURE_BINS == {
        COSET_NONNORMAL_LANE_METRIC: 16,
        COSET_NORMAL_LANE_METRIC: 16,
        COSET_BATCH_ORBIT_PROFILE_METRIC: 8,
    }
    assert first == second
    assert json.loads(json.dumps(first, sort_keys=True)) == first
    assert first["policy_sha256"] == dsl.policy_digest(policy)
    assert first["batch"]["candidate_count"] == 384
    assert len(first["batch"]["ordered_candidate_sha256"]) == 384
    assert sum(first["batch"]["aggregate_orbit_histogram"]) == 384
    assert len(first["lanes"]) == 46
    assert {lane["candidate_count"] for lane in first["lanes"]} == {8, 9}
    assert [(item["subgroup_normal"], item["action_count"], item["candidate_count"])
            for item in first["classes"]] == [
        (False, 45, 376),
        (True, 1, 8),
    ]
    assert all(
        len(lane["candidate_sha256"]) == lane["candidate_count"]
        and sum(lane["orbit_histogram"]) == lane["candidate_count"]
        for lane in first["lanes"]
    )
    unsigned = dict(first)
    descriptor_sha256 = unsigned.pop("descriptor_sha256")
    assert descriptor_sha256 == canonical_json_sha256(unsigned)
    for metric, coordinate in first["coordinates"].items():
        assert type(coordinate) is int
        assert 0 <= coordinate < COSET_FEATURE_BINS[metric]


def test_each_lane_changes_independently_for_offset_mutations():
    baseline = _descriptor(dsl.default_policy())
    for normal in (False, True):
        mutated = _descriptor(
            _mutated_policy(normal=normal, offset_delta=1)
        )
        assert _lane(mutated, normal=normal)["lane_sha256"] != (
            _lane(baseline, normal=normal)["lane_sha256"]
        )
        assert _lane(mutated, normal=not normal)["lane_sha256"] == (
            _lane(baseline, normal=not normal)["lane_sha256"]
        )
        assert _normality_class(mutated, normal=normal)["class_sha256"] != (
            _normality_class(baseline, normal=normal)["class_sha256"]
        )
        assert _normality_class(mutated, normal=not normal)["class_sha256"] == (
            _normality_class(baseline, normal=not normal)["class_sha256"]
        )
        other_metric = (
            COSET_NORMAL_LANE_METRIC
            if not normal
            else COSET_NONNORMAL_LANE_METRIC
        )
        assert mutated["coordinates"][other_metric] == (
            baseline["coordinates"][other_metric]
        )


def test_stride_and_explicit_support_change_only_their_lane_payload():
    baseline = _descriptor(dsl.default_policy())
    mutations = (
        _mutated_policy(normal=False, change_stride=True),
        _mutated_policy(normal=True, add_support=True),
    )
    for normal, policy in zip((False, True), mutations):
        mutated = _descriptor(policy)
        assert _lane(mutated, normal=normal)["lane_sha256"] != (
            _lane(baseline, normal=normal)["lane_sha256"]
        )
        assert _lane(mutated, normal=not normal)["lane_sha256"] == (
            _lane(baseline, normal=not normal)["lane_sha256"]
        )
        assert _normality_class(mutated, normal=normal)["class_sha256"] != (
            _normality_class(baseline, normal=normal)["class_sha256"]
        )
        assert mutated["batch"]["batch_sha256"] != (
            baseline["batch"]["batch_sha256"]
        )


def test_deterministic_policy_variants_occupy_multiple_cells():
    policies = [dsl.default_policy()]
    # More variants than a lane's 16 buckets makes this robust to individual
    # deterministic bucket collisions while still exercising actual walks.
    for normal in (False, True):
        policies.extend(
            _mutated_policy(normal=normal, offset_delta=delta)
            for delta in range(1, 21)
        )
    descriptors = [_descriptor(policy) for policy in policies]
    cells = {
        tuple(item["coordinates"][name] for name in COSET_FEATURE_DIMENSIONS)
        for item in descriptors
    }
    assert len(cells) > 1
    assert len({
        _lane(item, normal=False)["lane_sha256"] for item in descriptors
    }) > 1
    assert len({
        _lane(item, normal=True)["lane_sha256"] for item in descriptors
    }) > 1


def test_descriptor_is_catalog_order_deterministic():
    # The catalog API is allowed to return views in either order; the
    # descriptor artifact itself must retain one canonical action order.
    descriptor = _descriptor(dsl.default_policy())
    assert [lane["action_id"] for lane in descriptor["lanes"]] == sorted(
        view.action_id for view in action_search_views()
    )


def _map_program(
    program_id: str,
    coordinates: tuple[int, int, int],
    *,
    island: int,
    score: float,
) -> Program:
    return Program(
        id=program_id,
        code=f'{{"program":"{program_id}"}}',
        metrics={
            launcher.MAP_DESCRIPTOR_VERSION_METRIC: float(
                launcher.MAP_DESCRIPTOR_VERSION
            ),
            COSET_MAP_SCHEMA_METRIC: float(COSET_MAP_SCHEMA_VERSION),
            COSET_PROOF_LADDER_VERSION_METRIC: float(
                COSET_PROOF_LADDER_SCHEMA_VERSION
            ),
            **{
                name: float(value)
                for name, value in zip(COSET_FEATURE_DIMENSIONS, coordinates)
            },
            "combined_score": score,
        },
        metadata={"island": island},
    )


def test_fixed_coset_mapper_never_rescales_categories_to_midpoints():
    zero = _map_program("zero", (0, 0, 0), island=0, score=0.1)
    high = _map_program("high", (15, 15, 7), island=0, score=0.2)

    assert launcher._fixed_coset_feature_coords(
        zero, schema_version=COSET_MAP_SCHEMA_VERSION
    ) == [0, 0, 0]
    assert launcher._fixed_coset_feature_coords(
        high, schema_version=COSET_MAP_SCHEMA_VERSION
    ) == [15, 15, 7]
    zero.metrics[COSET_MAP_SCHEMA_METRIC] = 1.0
    try:
        launcher._fixed_coset_feature_coords(
            zero, schema_version=COSET_MAP_SCHEMA_VERSION
        )
    except RuntimeError as exc:
        assert "schema marker" in str(exc)
    else:
        raise AssertionError("legacy coset MAP schema was accepted")


def test_fixed_coset_map_rebuild_is_order_independent_and_tie_stable():
    programs = {
        item.id: item
        for item in (
            _map_program("b", (0, 0, 0), island=0, score=0.5),
            _map_program("a", (0, 0, 0), island=0, score=0.5),
            _map_program("c", (1, 2, 3), island=1, score=0.4),
            _map_program("d", (4, 5, 6), island=2, score=0.3),
            _map_program("e", (7, 8, 1), island=3, score=0.2),
        )
    }
    database = SimpleNamespace(
        programs=dict(reversed(list(programs.items()))),
        islands=[{"a", "b"}, {"c"}, {"d"}, {"e"}],
        island_feature_maps=[{} for _ in range(4)],
        archive=set(),
        feature_stats={"stale": {}},
        island_best_programs=[None] * 4,
        best_program_id=None,
        config=SimpleNamespace(archive_size=32),
    )

    launcher._rebuild_fixed_coset_feature_maps(
        database,
        schema_version=COSET_MAP_SCHEMA_VERSION,
    )

    assert database.island_feature_maps == [
        {"0-0-0": "a"},
        {"1-2-3": "c"},
        {"4-5-6": "d"},
        {"7-8-1": "e"},
    ]
    assert database.islands == [{"a"}, {"c"}, {"d"}, {"e"}]
    assert database.feature_stats == {}
    assert database.feature_bins_per_dim == COSET_FEATURE_BINS
