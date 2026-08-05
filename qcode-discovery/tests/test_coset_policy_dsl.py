from __future__ import annotations

import builtins
import copy
import json
from collections import Counter
from dataclasses import FrozenInstanceError
from math import comb

import pytest

from evolve import coset_policy_dsl as dsl
from evolve.coset_search_contract import (
    COSET_REPRESENTATION_ID,
    MAX_GENERATED_CANDIDATES,
    action_search_view,
    action_search_views,
    candidate_digest,
    normalize_candidate,
)


def _document(limit: int = 16) -> dict:
    return dsl.policy_document(dsl.default_policy(limit))


def _fresh_support(action_id: str, offset: int = 0) -> dict[str, list[int]]:
    action_search_view(action_id)  # Assert the helper is catalog-bound.
    return {
        "left": [offset, offset + 1],
        "right": [offset, offset + 1],
    }


def _action(document: dict, action_id: str) -> dict:
    return next(item for item in document["actions"] if item["action_id"] == action_id)


def test_current_catalog_has_the_two_contract_action_views():
    views = action_search_views()
    assert len(views) == dsl.REQUIRED_ACTION_VIEW_COUNT == 2
    assert {view.subgroup_normal for view in views} == {False, True}
    assert all(len(view.left_element_ids) >= 3 for view in views)
    assert all(len(view.right_element_ids) >= 3 for view in views)


def test_default_policy_renders_exact_bounded_round_robin_candidates():
    policy = dsl.default_policy(32)
    rows = dsl.render_candidates(policy)

    assert len(rows) == policy.candidate_limit == 32
    assert sum(action.quota for action in policy.actions) == 32
    counts = Counter(row["action_id"] for row in rows)
    assert counts == Counter({action.action_id: action.quota for action in policy.actions})
    assert len({candidate_digest(row) for row in rows}) == len(rows)
    for row in rows:
        view = action_search_view(row["action_id"])
        assert row == normalize_candidate(row)
        assert row["representation_id"] == COSET_REPRESENTATION_ID
        assert len(row["left_support"]) == len(row["right_support"]) == 3
        assert view.left_identity_id in row["left_support"]
        assert view.right_identity_id in row["right_support"]

    smaller_quota = min(action.quota for action in policy.actions)
    paired_prefix = rows[: 2 * smaller_quota]
    assert [row["action_id"] for row in paired_prefix] == [
        action.action_id
        for _ in range(smaller_quota)
        for action in policy.actions
    ]


def test_policy_and_candidate_rendering_are_canonical_and_order_independent():
    first = _document(16)
    action_id = first["actions"][0]["action_id"]
    supports = [_fresh_support(action_id, 0), _fresh_support(action_id, 2)]
    _action(first, action_id)["supports"] = supports

    second = copy.deepcopy(first)
    second["actions"].reverse()
    changed = _action(second, action_id)["supports"]
    changed.reverse()
    for support in changed:
        support["left"].reverse()
        support["right"].reverse()

    policy_one = dsl.normalize_policy(first)
    policy_two = dsl.normalize_policy(second)
    assert policy_one == policy_two
    assert dsl.canonical_policy_json(policy_one) == dsl.canonical_policy_json(policy_two)
    assert dsl.policy_digest(policy_one) == dsl.policy_digest(policy_two)
    assert dsl.render_candidates(policy_one) == dsl.render_candidates(policy_two)


def test_canonical_policy_round_trip_and_jsonl_render():
    policy = dsl.default_policy()
    canonical = dsl.canonical_policy_json(policy)
    reparsed = dsl.parse_policy(canonical)
    jsonl = dsl.render_candidate_jsonl(reparsed)

    assert reparsed == policy
    assert canonical == dsl.canonical_policy_json(reparsed)
    assert jsonl.endswith("\n")
    assert len(jsonl.splitlines()) == MAX_GENERATED_CANDIDATES
    assert [json.loads(line) for line in jsonl.splitlines()] == dsl.render_candidates(policy)


def test_full_384_candidate_set_migrates_to_compact_exact_anchor_policy():
    source = dsl.render_candidates(dsl.default_policy())
    migrated = dsl.policy_from_candidates(list(reversed(source)))
    canonical = dsl.canonical_policy_json(migrated)
    replayed = dsl.render_candidates(migrated)

    assert len(source) == len(replayed) == MAX_GENERATED_CANDIDATES
    assert len(canonical.encode("utf-8")) < 30_000
    assert {candidate_digest(row) for row in replayed} == {
        candidate_digest(row) for row in source
    }
    assert all(not action.include_published for action in migrated.actions)
    assert all(not action.walk.enabled for action in migrated.actions)
    assert sum(len(action.supports) for action in migrated.actions) == 384
    document = dsl.policy_document(migrated)
    assert all(
        type(index) is int
        for action in document["actions"]
        for support in action["supports"]
        for side in (support["left"], support["right"])
        for index in side
    )
    assert all(
        len(support[side]) == 2
        for action in document["actions"]
        for support in action["supports"]
        for side in ("left", "right")
    )


def test_candidate_migration_deduplicates_and_is_order_canonical():
    source = dsl.render_candidates(dsl.default_policy(8))
    one = dsl.policy_from_candidates(source + [copy.deepcopy(source[0])])
    two = dsl.policy_from_candidates(list(reversed(source)))

    assert one == two
    assert one.candidate_limit == 8
    assert dsl.canonical_policy_json(one) == dsl.canonical_policy_json(two)


def test_candidate_migration_requires_normalized_rows_and_both_action_lanes():
    source = dsl.render_candidates(dsl.default_policy(8))
    changed = copy.deepcopy(source)
    changed[0]["left_support"].reverse()
    with pytest.raises(dsl.CosetPolicyError, match="not already normalized"):
        dsl.policy_from_candidates(changed)

    first_action = source[0]["action_id"]
    one_lane = [row for row in source if row["action_id"] == first_action]
    with pytest.raises(dsl.CosetPolicyError, match="cover both"):
        dsl.policy_from_candidates(one_lane)


@pytest.mark.parametrize(
    ("scope", "mutation"),
    [
        ("root-extra", lambda row: row.__setitem__("python", "pass")),
        ("root-missing", lambda row: row.pop("renderer")),
        (
            "action-extra",
            lambda row: row["actions"][0].__setitem__("distance_claim", 99),
        ),
        (
            "walk-extra",
            lambda row: row["actions"][0]["walk"].__setitem__("callable", "f"),
        ),
        (
            "support-extra",
            lambda row: (
                row["actions"][0].__setitem__(
                    "supports", [_fresh_support(row["actions"][0]["action_id"])]
                ),
                row["actions"][0]["supports"][0].__setitem__("score", 1),
            ),
        ),
    ],
)
def test_every_object_uses_an_exact_schema(scope, mutation):
    document = _document()
    mutation(document)
    with pytest.raises(dsl.CosetPolicyError, match="fields are not exact"):
        dsl.normalize_policy(document)


@pytest.mark.parametrize(
    "mutation",
    [
        lambda row: row.__setitem__("candidate_limit", True),
        lambda row: row["actions"][0].__setitem__("quota", 1.0),
        lambda row: row["actions"][0].__setitem__("include_published", 1),
        lambda row: row["actions"][0]["walk"].__setitem__("offset", False),
        lambda row: row["actions"][0].__setitem__("supports", ()),
        lambda row: row.__setitem__("support_split", (3, 3)),
        lambda row: row.__setitem__("renderer", None),
    ],
)
def test_only_builtin_declarative_json_types_are_accepted(mutation):
    document = _document()
    mutation(document)
    with pytest.raises(dsl.CosetPolicyError):
        dsl.normalize_policy(document)


def test_exotic_python_values_are_rejected_before_comparison():
    comparisons = []

    class ExecutableEquality:
        def __eq__(self, _other):
            comparisons.append("called")
            return True

    document = _document()
    document["representation_id"] = ExecutableEquality()
    with pytest.raises(dsl.CosetPolicyError, match="only JSON"):
        dsl.normalize_policy(document)
    assert comparisons == []


def test_text_subclasses_cannot_supply_executable_decode_or_encode_hooks():
    calls = []

    class ExecutableText(str):
        def encode(self, *_args, **_kwargs):
            calls.append("called")
            return super().encode(*_args, **_kwargs)

    payload = ExecutableText(dsl.canonical_policy_json(dsl.default_policy()))
    with pytest.raises(dsl.CosetPolicyError, match="JSON text or bytes"):
        dsl.parse_policy(payload)
    assert calls == []


def test_json_parser_rejects_duplicate_keys_constants_and_python_source():
    with pytest.raises(dsl.CosetPolicyError, match="duplicate JSON object key"):
        dsl.parse_policy('{"schema_version":1,"schema_version":1}')
    with pytest.raises(dsl.CosetPolicyError, match="non-finite JSON number"):
        dsl.parse_policy('{"candidate_limit":NaN}')
    with pytest.raises(dsl.CosetPolicyError, match="not strict JSON"):
        dsl.parse_policy("__import__('os').system('false')")


def test_valid_parse_and_render_never_call_python_eval_or_exec(monkeypatch):
    def forbidden(*_args, **_kwargs):
        raise AssertionError("Python execution primitive was called")

    payload = dsl.canonical_policy_json(dsl.default_policy())
    monkeypatch.setattr(builtins, "eval", forbidden)
    monkeypatch.setattr(builtins, "exec", forbidden)

    policy = dsl.parse_policy(payload)
    assert len(dsl.render_candidates(policy)) == MAX_GENERATED_CANDIDATES


@pytest.mark.parametrize("candidate_limit", [2, 383])
def test_production_parser_requires_the_full_candidate_portfolio(candidate_limit):
    policy = dsl.default_policy(candidate_limit)

    # Trusted normalization/rendering remains available for bounded migrations.
    assert dsl.normalize_policy(dsl.policy_document(policy)) == policy
    assert len(dsl.render_candidates(policy)) == candidate_limit
    with pytest.raises(dsl.CosetPolicyError, match="must be exactly 384"):
        dsl.parse_policy(dsl.canonical_policy_json(policy))


@pytest.mark.parametrize("quotas", [(192, 192), (287, 97)])
def test_production_parser_requires_exact_catalog_derived_lane_quotas(quotas):
    document = _document(MAX_GENERATED_CANDIDATES)
    for action, quota in zip(document["actions"], quotas, strict=True):
        action["quota"] = quota

    # The generic schema permits alternative balanced lane allocations for
    # trusted migrations; untrusted evolved text may not use them to game the
    # portfolio composition.
    normalized = dsl.normalize_policy(document)
    assert tuple(action.quota for action in normalized.actions) == quotas
    with pytest.raises(dsl.CosetPolicyError, match="quota must be exactly"):
        dsl.parse_policy(json.dumps(document))


def test_production_parser_requires_the_catalog_published_anchor_selection():
    document = _document(MAX_GENERATED_CANDIDATES)
    published_view = next(
        view for view in action_search_views() if view.published_left_support is not None
    )
    lane = _action(document, published_view.action_id)
    assert lane["include_published"] is True
    lane["include_published"] = False

    # Historical/migration normalization remains flexible, but production
    # evolved text cannot drop the regression anchor.
    normalized = dsl.normalize_policy(document)
    assert next(
        action
        for action in normalized.actions
        if action.action_id == published_view.action_id
    ).include_published is False
    with pytest.raises(dsl.CosetPolicyError, match="include_published must be exactly true"):
        dsl.parse_policy(json.dumps(document))


def test_python_text_in_a_whitelisted_identifier_position_is_rejected(tmp_path):
    sentinel = tmp_path / "must-not-exist"
    document = _document()
    document["actions"][0]["action_id"] = (
        f"__import__('pathlib').Path({str(sentinel)!r}).touch()"
    )
    payload = json.dumps(document)

    with pytest.raises(dsl.CosetPolicyError, match="unknown coset action_id"):
        dsl.parse_policy(payload)
    assert not sentinel.exists()


def test_policy_byte_and_candidate_caps_are_enforced():
    with pytest.raises(dsl.CosetPolicyError, match="payload must contain"):
        dsl.parse_policy(b" " * (dsl.MAX_POLICY_BYTES + 1))

    document = _document()
    document["candidate_limit"] = MAX_GENERATED_CANDIDATES + 1
    document["actions"][0]["quota"] += 1
    with pytest.raises(dsl.CosetPolicyError, match="candidate_limit"):
        dsl.normalize_policy(document)

    document = _document()
    action = document["actions"][0]
    action["supports"] = [
        _fresh_support(action["action_id"])
        for _ in range(dsl.MAX_EXPLICIT_SUPPORTS_PER_ACTION + 1)
    ]
    with pytest.raises(dsl.CosetPolicyError, match="support cap"):
        dsl.normalize_policy(document)


def test_catalog_action_and_support_index_whitelists_are_enforced():
    unknown_action = _document()
    unknown_action["actions"][0]["action_id"] = "not-in-the-catalog"
    with pytest.raises(dsl.CosetPolicyError, match="unknown coset action_id"):
        dsl.normalize_policy(unknown_action)

    views = action_search_views()
    action_id = views[0].action_id
    out_of_range = _document()
    support = _fresh_support(action_id)
    support["left"][1] = len(action_search_view(action_id).left_element_ids)
    _action(out_of_range, action_id)["supports"] = [support]
    with pytest.raises(dsl.CosetPolicyError, match="out of range"):
        dsl.normalize_policy(out_of_range)

    duplicate_index = _document()
    support = _fresh_support(action_id)
    support["left"] = [1, 1]
    _action(duplicate_index, action_id)["supports"] = [support]
    with pytest.raises(dsl.CosetPolicyError, match="duplicate or out of range"):
        dsl.normalize_policy(duplicate_index)


def test_production_split_duplicates_and_catalog_binding_fail_closed():
    action_id = action_search_views()[0].action_id

    wrong_split = _document()
    support = _fresh_support(action_id)
    support["left"].append(3)
    _action(wrong_split, action_id)["supports"] = [support]
    with pytest.raises(dsl.CosetPolicyError, match="exactly two nonidentity"):
        dsl.normalize_policy(wrong_split)

    duplicate = _document()
    support = _fresh_support(action_id)
    _action(duplicate, action_id)["supports"] = [support, copy.deepcopy(support)]
    with pytest.raises(dsl.CosetPolicyError, match="duplicate supports"):
        dsl.normalize_policy(duplicate)

    wrong_catalog = _document()
    wrong_catalog["action_catalog_sha256"] = "0" * 64
    with pytest.raises(dsl.CosetPolicyError, match="catalog binding changed"):
        dsl.normalize_policy(wrong_catalog)


def test_action_set_quota_and_published_support_contracts_are_exact():
    document = _document()
    document["actions"][1] = copy.deepcopy(document["actions"][0])
    with pytest.raises(dsl.CosetPolicyError, match="duplicate coset action_id"):
        dsl.normalize_policy(document)

    document = _document()
    document["actions"][0]["quota"] -= 1
    with pytest.raises(dsl.CosetPolicyError, match="sum of action quotas"):
        dsl.normalize_policy(document)

    no_published_view = next(
        view for view in action_search_views() if view.published_left_support is None
    )
    document = _document()
    _action(document, no_published_view.action_id)["include_published"] = True
    with pytest.raises(dsl.CosetPolicyError, match="has no published support"):
        dsl.normalize_policy(document)


def test_pair_walk_is_bounded_coprime_and_canonical_when_disabled():
    view = next(view for view in action_search_views() if view.subgroup_normal)
    pair_space = comb(len(view.left_element_ids) - 1, 2) * comb(
        len(view.right_element_ids) - 1, 2
    )
    assert pair_space % 5 == 0

    non_coprime = _document()
    _action(non_coprime, view.action_id)["walk"]["stride"] = 5
    with pytest.raises(dsl.CosetPolicyError, match="coprime"):
        dsl.normalize_policy(non_coprime)

    out_of_range = _document()
    _action(out_of_range, view.action_id)["walk"]["offset"] = pair_space
    with pytest.raises(dsl.CosetPolicyError, match="walk.offset"):
        dsl.normalize_policy(out_of_range)

    disabled = _document()
    lane = _action(disabled, view.action_id)
    lane["walk"] = {"enabled": False, "offset": 1, "stride": 1}
    with pytest.raises(dsl.CosetPolicyError, match="canonical offset"):
        dsl.normalize_policy(disabled)

    disabled = _document()
    lane = _action(disabled, view.action_id)
    lane["walk"] = {"enabled": False, "offset": 0, "stride": 1}
    with pytest.raises(dsl.CosetPolicyError, match="enabled walk"):
        dsl.normalize_policy(disabled)


def test_typed_policy_is_frozen_and_render_rechecks_catalog(monkeypatch):
    policy = dsl.default_policy(8)
    with pytest.raises(FrozenInstanceError):
        policy.candidate_limit = 9

    monkeypatch.setattr(dsl, "_catalog_sha256", lambda: "0" * 64)
    with pytest.raises(dsl.CosetPolicyError, match="changed after policy validation"):
        dsl.render_candidates(policy)


def test_manually_constructed_typed_value_cannot_bypass_schema_validation():
    valid = dsl.default_policy(8)
    invalid = dsl.CosetPolicy(
        action_catalog_sha256=valid.action_catalog_sha256,
        candidate_limit=MAX_GENERATED_CANDIDATES + 1,
        actions=valid.actions,
    )
    with pytest.raises(dsl.CosetPolicyError, match="candidate_limit"):
        dsl.policy_document(invalid)
    with pytest.raises(dsl.CosetPolicyError, match="candidate_limit"):
        dsl.render_candidates(invalid)


def test_default_policy_limit_is_strict_integer_and_capped():
    for invalid in (True, 1, 2.0, MAX_GENERATED_CANDIDATES + 1):
        with pytest.raises(dsl.CosetPolicyError):
            dsl.default_policy(invalid)
