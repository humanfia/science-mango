from __future__ import annotations

import copy
import hashlib
import json
import pickle
import threading

import numpy as np
import pytest

from evaluation import paper400_dic5_optimized_cnf_final_v13 as optimized
from investigations import paper400_dic5_adaptive_leaf_overlay_v2 as overlay
from investigations import paper400_dic5_cube16 as cube16
from investigations import paper400_dic5_nested_width10_campaign_v1 as width10
from investigations import paper400_dic5_widened_parent_campaign_v1 as width6


PARENT_INDEX = 0
GLOBAL_LEAF_INDEX = 0
CANDIDATES = (16, 15)


def _synthetic_instance() -> optimized.OptimizedInstance:
    """Leave physical 15+ free and make DIMACS 401 a real auxiliary variable."""

    hx = np.zeros((200, 400), dtype=np.uint8)
    hz = np.zeros_like(hx)
    lx = np.zeros((16, 400), dtype=np.uint8)
    lx[0, 0] = 1
    lz = np.zeros_like(lx)
    cnf = {
        "num_variables": 405,
        "num_clauses": 0,
        "operator_variables": list(range(1, 401)),
        "logical_variables": [1],
        "native_atmost": None,
        "clauses": [],
    }
    cnf["cnf_sha256"] = optimized.canonical_sha256({
        "num_variables": cnf["num_variables"],
        "clauses": cnf["clauses"],
        "native_atmost": None,
    })
    report = optimized.seal({
        "schema_version": 1,
        "solver_invoked": False,
        "baseline": {"preflight_sha256": "a" * 64},
    }, "report_sha256")
    return optimized.OptimizedInstance(
        hx=hx,
        hz=hz,
        lx=lx,
        lz=lz,
        basis_checks=hx[:192].copy(),
        active_logical=lx[:1].copy(),
        cnf=cnf,
        dimacs=optimized.render_dimacs(cnf),
        report=report,
    )


@pytest.fixture(scope="module")
def material() -> dict[str, object]:
    instance = _synthetic_instance()
    parent = cube16.build_coverage_manifest(
        instance,
        strict_base=False,
        split_variables=(1, 2, 3, 4),
    )
    widened = width6.build_campaign_manifest(
        parent,
        instance,
        parent_cube_index=PARENT_INDEX,
        strict_base=False,
    )
    preview = width10.preview_extension_variables(
        widened,
        parent,
        instance,
        parent_cube_index=PARENT_INDEX,
        strict_base=False,
    )
    campaign = width10.build_campaign_manifest(
        widened,
        parent,
        instance,
        confirmed_extension_variables=preview[
            "proposed_extension_variables_dimacs"
        ],
        parent_cube_index=PARENT_INDEX,
        strict_base=False,
    )
    campaign_verification = width10.verify_campaign_manifest(
        campaign,
        widened,
        parent,
        instance,
        parent_cube_index=PARENT_INDEX,
        strict_base=False,
    )
    assert campaign_verification["valid"] is True
    parent_payload = width10.verified_child_dimacs_from_verification(
        campaign,
        widened,
        parent,
        instance,
        verification_record=campaign_verification,
        global_leaf_index=GLOBAL_LEAF_INDEX,
        parent_cube_index=PARENT_INDEX,
        strict_base=False,
    )
    evidence = overlay.build_hard_evidence_record(
        campaign,
        global_leaf_index=GLOBAL_LEAF_INDEX,
        status="TIMEOUT",
        runner_record_sha256="1" * 64,
        result_record_sha256="2" * 64,
        timeout_seconds=60.0,
        elapsed_seconds=60.5,
        timed_out=True,
    )
    manifest = overlay.build_overlay_manifest(
        campaign,
        widened,
        parent,
        instance,
        global_leaf_index=GLOBAL_LEAF_INDEX,
        hard_evidence=evidence,
        expected_hard_evidence_sha256=evidence["evidence_sha256"],
        candidate_variables=CANDIDATES,
        strict_base=False,
    )
    return {
        "instance": instance,
        "parent": parent,
        "widened": widened,
        "campaign": campaign,
        "campaign_verification": campaign_verification,
        "parent_payload": parent_payload,
        "evidence": evidence,
        "manifest": manifest,
    }


def _reseal_evidence(evidence: dict) -> dict:
    changed = copy.deepcopy(evidence)
    changed.pop("evidence_sha256", None)
    return overlay.seal(changed, "evidence_sha256")


def _build_with(material: dict[str, object], **changes: object) -> dict:
    arguments = {
        "global_leaf_index": GLOBAL_LEAF_INDEX,
        "hard_evidence": material["evidence"],
        "expected_hard_evidence_sha256": material["evidence"][
            "evidence_sha256"
        ],
        "candidate_variables": CANDIDATES,
        "strict_base": False,
    }
    arguments.update(changes)
    return overlay.build_overlay_manifest(
        material["campaign"],
        material["widened"],
        material["parent"],
        material["instance"],
        **arguments,
    )


def test_real_width10_replay_verified_bytes_and_overlay_pin(
    material: dict[str, object],
) -> None:
    manifest = material["manifest"]
    evidence = material["evidence"]
    record = overlay.verify_overlay_manifest(
        manifest,
        material["campaign"],
        material["widened"],
        material["parent"],
        material["instance"],
        global_leaf_index=GLOBAL_LEAF_INDEX,
        hard_evidence=evidence,
        expected_hard_evidence_sha256=evidence["evidence_sha256"],
        candidate_variables=CANDIDATES,
        expected_overlay_sha256=manifest["manifest_sha256"],
        strict_base=False,
    )
    assert record["valid"] is True
    assert record["current_source_exact_replay"] is True
    assert record["mutually_exclusive"] is True
    assert record["exhaustive"] is True
    assert record["parent_formula_equivalence_certified"] is True
    assert record["expected_overlay_sha256"] == manifest["manifest_sha256"]
    assert set(record) == overlay.VERIFICATION_FIELDS
    assert overlay.selfhash_valid(record, "record_sha256")
    parent_scope = manifest["parent_scope"]
    assert parent_scope["verified_child_payload_sha256"] == hashlib.sha256(
        material["parent_payload"]
    ).hexdigest()
    assert parent_scope["verified_child_payload_bytes"] == len(
        material["parent_payload"]
    )


def test_complete_root_width6_width10_ancestry_is_hash_closed(
    material: dict[str, object],
) -> None:
    manifest = material["manifest"]
    ancestry = manifest["ancestry"]
    chain = ancestry["chain"]
    assert ancestry["chain_roles"] == [
        "root-width4",
        "selected-width6",
        "selected-width10-leaf",
    ]
    assert chain[0]["manifest_sha256"] == material["parent"]["manifest_sha256"]
    assert chain[1]["manifest_sha256"] == material["widened"]["manifest_sha256"]
    assert chain[2]["manifest_sha256"] == material["campaign"]["manifest_sha256"]
    assert chain[2]["leaf_sha256"] == material["campaign"]["leaves"][0][
        "leaf_sha256"
    ]
    assert chain[2]["full_verification_record_sha256"] == material[
        "campaign_verification"
    ]["record_sha256"]
    assert overlay.selfhash_valid(chain[0], "root_ancestry_sha256")
    assert overlay.selfhash_valid(chain[1], "width6_ancestry_sha256")
    assert overlay.selfhash_valid(chain[2], "width10_ancestry_sha256")
    assert overlay.selfhash_valid(ancestry, "ancestry_sha256")


def test_one_hard_evidence_yields_exactly_one_pending_binary_frontier(
    material: dict[str, object],
) -> None:
    manifest = material["manifest"]
    policy = manifest["candidate_policy"]
    adaptive_manifest = manifest["adaptive_manifest"]
    assert policy["candidate_variables"] == [15, 16]
    assert policy["selected_variable"] == 15
    assert policy["hard_evidence_records_consumed"] == 1
    assert policy["authorized_split_count"] == 1
    assert policy["max_depth"] == 1
    assert policy["max_nodes"] == 3
    assert policy["descendant_refinement_authorized"] is False
    assert policy["next_round_requires_new_hard_evidence"] is True
    assert policy["next_round_requires_prior_overlay_hash_chain"] is True
    assert policy["fixed_multi-level-lookahead_authorized"] is False
    assert len(adaptive_manifest["tree"]["nodes"]) == 3
    assert len(adaptive_manifest["tree"]["local_covers"]) == 1
    assert [item["observed_status"] for item in manifest["descendants"]] == [
        "PENDING",
        "PENDING",
    ]
    assert [item["status_source"] for item in manifest["descendants"]] == [
        "generated-frontier-v1",
        "generated-frontier-v1",
    ]
    assert all(item["pending"] is True for item in manifest["descendants"])
    assert manifest["test_only"] is True
    assert manifest["production_eligible"] is False
    assert manifest["launch_authorized"] is False
    assert manifest["publication_certificate"] is False


def test_descendant_relative_units_dimacs_hash_bytes_counts_and_cover(
    material: dict[str, object],
) -> None:
    manifest = material["manifest"]
    parent_payload = material["parent_payload"]
    parent_units = manifest["parent_scope"]["combined_unit_clauses"]
    assert manifest["local_cover"]["split_variable"] == 15
    assert manifest["local_cover"]["mutually_exclusive"] is True
    assert manifest["local_cover"]["exhaustive"] is True
    for descendant, literal in zip(
        manifest["descendants"], (15, -15), strict=True
    ):
        assert descendant["relative_assignment_literals"] == [literal]
        assert descendant["relative_unit_clauses"] == [[literal]]
        assert descendant["combined_unit_clauses"] == parent_units + [[literal]]
        payload = overlay.adaptive.render_cube_dimacs(parent_payload, [literal])
        parsed = overlay.adaptive.parse_dimacs(payload)
        assert descendant["child_dimacs_sha256"] == hashlib.sha256(
            payload
        ).hexdigest()
        assert descendant["child_dimacs_bytes"] == len(payload)
        assert descendant["child_num_variables"] == 405
        assert descendant["child_num_clauses"] == parsed["num_clauses"]
        assert descendant["child_num_clauses"] == (
            manifest["parent_scope"]["child_num_clauses"] + 1
        )
        assert overlay.selfhash_valid(descendant, "descendant_sha256")


def test_auxiliary_and_already_fixed_candidates_fail_closed(
    material: dict[str, object],
) -> None:
    with pytest.raises(overlay.AdaptiveLeafOverlayError, match="physical range"):
        _build_with(material, candidate_variables=(401,))
    with pytest.raises(overlay.AdaptiveLeafOverlayError, match="already fixed"):
        _build_with(material, candidate_variables=(14, 15))
    with pytest.raises(overlay.AdaptiveLeafOverlayError, match="physical range"):
        _build_with(material, candidate_variables=(True,))


@pytest.mark.parametrize("tamper", ["leaf", "child_cnf"])
def test_resealed_hard_evidence_wrong_leaf_or_cnf_fails_binding(
    material: dict[str, object], tamper: str,
) -> None:
    changed = copy.deepcopy(material["evidence"])
    if tamper == "leaf":
        changed["global_leaf_index"] = 1
    else:
        changed["child_cnf_sha256"] = "f" * 64
    changed = _reseal_evidence(changed)
    with pytest.raises(overlay.AdaptiveLeafOverlayError, match="binds the wrong leaf"):
        _build_with(
            material,
            hard_evidence=changed,
            expected_hard_evidence_sha256=changed["evidence_sha256"],
        )


def test_fully_resealed_hard_evidence_cannot_cross_external_pin(
    material: dict[str, object],
) -> None:
    changed = copy.deepcopy(material["evidence"])
    changed["runner_record_sha256"] = "3" * 64
    changed = _reseal_evidence(changed)
    with pytest.raises(overlay.AdaptiveLeafOverlayError, match="external SHA-256 pin"):
        _build_with(material, hard_evidence=changed)


def test_external_overlay_pin_and_strict_json_types_fail_closed(
    material: dict[str, object],
) -> None:
    manifest = material["manifest"]
    evidence = material["evidence"]
    common = {
        "global_leaf_index": GLOBAL_LEAF_INDEX,
        "hard_evidence": evidence,
        "expected_hard_evidence_sha256": evidence["evidence_sha256"],
        "candidate_variables": CANDIDATES,
        "strict_base": False,
    }
    with pytest.raises(overlay.AdaptiveLeafOverlayError, match="external SHA-256 pin"):
        overlay.verify_overlay_manifest(
            manifest,
            material["campaign"],
            material["widened"],
            material["parent"],
            material["instance"],
            expected_overlay_sha256="f" * 64,
            **common,
        )
    tuple_tamper = copy.deepcopy(manifest)
    tuple_tamper["descendants"][0]["relative_assignment_literals"] = (15,)
    with pytest.raises(overlay.AdaptiveLeafOverlayError, match="non-JSON type tuple"):
        overlay.verify_overlay_manifest(
            tuple_tamper,
            material["campaign"],
            material["widened"],
            material["parent"],
            material["instance"],
            expected_overlay_sha256=manifest["manifest_sha256"],
            **common,
        )
    with pytest.raises(overlay.AdaptiveLeafOverlayError, match="strict integer"):
        overlay.verify_overlay_manifest(
            manifest,
            material["campaign"],
            material["widened"],
            material["parent"],
            material["instance"],
            global_leaf_index=True,
            hard_evidence=evidence,
            expected_hard_evidence_sha256=evidence["evidence_sha256"],
            candidate_variables=CANDIDATES,
            expected_overlay_sha256=manifest["manifest_sha256"],
            strict_base=False,
        )




def _token_scope(material: dict[str, object]):
    return overlay.acquire_campaign_replay_token(
        material["campaign"],
        material["widened"],
        material["parent"],
        material["instance"],
        expected_width10_campaign_sha256=material["campaign"][
            "manifest_sha256"
        ],
        expected_width6_campaign_sha256=material["widened"][
            "manifest_sha256"
        ],
        expected_parent_manifest_sha256=material["parent"][
            "manifest_sha256"
        ],
        strict_base=False,
    )


def _consume_token(
    material: dict[str, object], token: object,
) -> dict[str, object]:
    return overlay._campaign_replay_verification(
        token,
        material["campaign"],
        material["widened"],
        material["parent"],
        material["instance"],
        strict_base=False,
    )


def test_default_path_still_performs_one_full_replay(
    material: dict[str, object], monkeypatch: pytest.MonkeyPatch,
) -> None:
    calls = 0
    original = width10.verify_campaign_manifest

    def counted(*args, **kwargs):
        nonlocal calls
        calls += 1
        return original(*args, **kwargs)

    monkeypatch.setattr(width10, "verify_campaign_manifest", counted)
    rebuilt = _build_with(material)
    assert overlay.json_type_equal(rebuilt, material["manifest"])
    assert calls == 1


def test_active_token_reuses_one_full_replay_and_matches_default(
    material: dict[str, object], monkeypatch: pytest.MonkeyPatch,
) -> None:
    calls = 0
    original = width10.verify_campaign_manifest

    def counted(*args, **kwargs):
        nonlocal calls
        calls += 1
        return original(*args, **kwargs)

    monkeypatch.setattr(width10, "verify_campaign_manifest", counted)
    with _token_scope(material) as token:
        rebuilt = _build_with(
            material, _campaign_replay_token=token
        )
        record = overlay.verify_overlay_manifest(
            material["manifest"],
            material["campaign"],
            material["widened"],
            material["parent"],
            material["instance"],
            global_leaf_index=GLOBAL_LEAF_INDEX,
            hard_evidence=material["evidence"],
            expected_hard_evidence_sha256=material["evidence"][
                "evidence_sha256"
            ],
            candidate_variables=CANDIDATES,
            expected_overlay_sha256=material["manifest"][
                "manifest_sha256"
            ],
            strict_base=False,
            _campaign_replay_token=token,
        )
    assert overlay.json_type_equal(rebuilt, material["manifest"])
    assert record["valid"] is True
    assert calls == 1
    with pytest.raises(
        overlay.AdaptiveLeafOverlayError,
        match="owner/input binding",
    ):
        _consume_token(material, token)


def test_token_is_immutable_nonserializable_and_cross_thread_poisoned(
    material: dict[str, object],
) -> None:
    failures: list[BaseException] = []
    with _token_scope(material) as token:
        with pytest.raises(TypeError, match="immutable"):
            token._active = False
        with pytest.raises(TypeError, match="non-copyable"):
            copy.copy(token)
        with pytest.raises(TypeError, match="non-copyable"):
            copy.deepcopy(token)
        with pytest.raises(TypeError, match="non-serializable"):
            pickle.dumps(token)
        with pytest.raises(TypeError):
            json.dumps(token)

        fake = object.__new__(overlay._CampaignReplayToken)
        with pytest.raises(overlay.AdaptiveLeafOverlayError):
            _consume_token(material, fake)

        def foreign_use() -> None:
            try:
                _consume_token(material, token)
            except BaseException as exc:
                failures.append(exc)

        thread = threading.Thread(target=foreign_use)
        thread.start()
        thread.join()
        assert len(failures) == 1
        assert isinstance(failures[0], overlay.AdaptiveLeafOverlayError)
        with pytest.raises(
            overlay.AdaptiveLeafOverlayError,
            match="owner/input binding",
        ):
            _consume_token(material, token)


def test_token_rejects_resealed_input_and_instance_matrix_mutation(
    material: dict[str, object],
) -> None:
    changed_campaign = copy.deepcopy(material["campaign"])
    changed_material = dict(material)
    changed_material["campaign"] = changed_campaign
    with _token_scope(changed_material) as token:
        changed_campaign["test_only"] = False
        changed_campaign.pop("manifest_sha256")
        changed_campaign["manifest_sha256"] = overlay.canonical_sha256(
            changed_campaign
        )
        with pytest.raises(
            overlay.AdaptiveLeafOverlayError,
            match="content binding",
        ):
            _consume_token(changed_material, token)

    changed_instance = copy.deepcopy(material["instance"])
    changed_material = dict(material)
    changed_material["instance"] = changed_instance
    with _token_scope(changed_material) as token:
        changed_instance.hx[0, 0] ^= 2
        with pytest.raises(
            overlay.AdaptiveLeafOverlayError,
            match="content binding",
        ):
            _consume_token(changed_material, token)


def test_token_rejects_callable_drift_and_bad_pin_before_full_replay(
    material: dict[str, object], monkeypatch: pytest.MonkeyPatch,
) -> None:
    with _token_scope(material) as token:
        monkeypatch.setattr(
            width10,
            "_validate_fast_boundary",
            lambda *args, **kwargs: None,
        )
        with pytest.raises(
            overlay.AdaptiveLeafOverlayError,
            match="content binding",
        ):
            _consume_token(material, token)
    monkeypatch.undo()

    calls = 0
    original = width10.verify_campaign_manifest

    def counted(*args, **kwargs):
        nonlocal calls
        calls += 1
        return original(*args, **kwargs)

    monkeypatch.setattr(width10, "verify_campaign_manifest", counted)
    with pytest.raises(
        overlay.AdaptiveLeafOverlayError,
        match="external SHA-256 pin",
    ):
        with overlay.acquire_campaign_replay_token(
            material["campaign"],
            material["widened"],
            material["parent"],
            material["instance"],
            expected_width10_campaign_sha256="f" * 64,
            expected_width6_campaign_sha256=material["widened"][
                "manifest_sha256"
            ],
            expected_parent_manifest_sha256=material["parent"][
                "manifest_sha256"
            ],
            strict_base=False,
        ):
            pytest.fail("a bad external pin yielded a token")
    assert calls == 0



def test_token_detects_mutation_during_fast_boundary(
    material: dict[str, object], monkeypatch: pytest.MonkeyPatch,
) -> None:
    changed_instance = copy.deepcopy(material["instance"])
    changed_material = dict(material)
    changed_material["instance"] = changed_instance
    original = width10._validate_fast_boundary
    armed = False

    def mutating_boundary(*args, **kwargs):
        result = original(*args, **kwargs)
        if armed:
            changed_instance.hx[0, 0] ^= 1
        return result

    monkeypatch.setattr(
        width10, "_validate_fast_boundary", mutating_boundary
    )
    with _token_scope(changed_material) as token:
        armed = True
        with pytest.raises(
            overlay.AdaptiveLeafOverlayError,
            match="changed during fast-boundary use",
        ):
            _build_with(
                changed_material, _campaign_replay_token=token
            )
