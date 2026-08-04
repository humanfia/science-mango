"""Crash-recovery contract for policy-v3 representation handoffs."""

from __future__ import annotations

import copy
from dataclasses import replace
from pathlib import Path
from typing import Any

import pytest

import humanize.flow as flow_module
from humanize.flow import FlowConfig, HumanizeFlow, RoundTransactionError
from humanize.pipeline import FiveStagePipeline
from humanize.state import atomic_write_jsonl


MAX_ROUNDS = 12
RUN_ID = "policy-v3-round12-recovery"


@pytest.fixture
def sealed_exact_classifier(monkeypatch: pytest.MonkeyPatch) -> None:
    """Keep this transaction test independent of formal solver fixtures.

    The summaries and their source JSONL bytes remain hash/row-count bound and
    are replayed from disk.  Formal-checkpoint semantics are tested separately;
    here a schema-v2, round-bound test row represents an exact audit result.
    """

    monkeypatch.setattr(
        flow_module,
        "classify_evaluation",
        lambda _row: flow_module.AuditOutcome.EXACT,
    )


def _sealed_round_history(rounds_root: Path) -> tuple[list[dict[str, Any]], dict[str, Any]]:
    """Create four exact-d2 rounds followed by eight evidence-neutral rounds."""

    rounds: list[dict[str, Any]] = []
    regime: dict[str, Any] = flow_module._normal_search_regime(0)
    for number in range(1, MAX_ROUNDS + 1):
        round_dir = rounds_root / f"round-{number:03d}"
        round_dir.mkdir(parents=True, exist_ok=True)
        rows = []
        if number <= 4:
            rows.append({
                "n": 360,
                "k": 8,
                "d": 2,
                "d_is_exact": True,
                "stage": "exact",
                "audit_attempt": {
                    "schema_version": 2,
                    "round": number,
                    "evidence": {"test_fixture": True},
                },
            })
        identity = atomic_write_jsonl(round_dir / "milp.jsonl", rows)
        sealed = flow_module._sealed_round_exact_summary(
            round_number=number,
            round_dir=round_dir,
            failure_feedback={
                "source_milp_sha256": identity["sha256"],
                "source_milp_bytes": identity["bytes"],
                "source_milp_rows": identity["rows"],
            },
        )
        summary = {
            "round": number,
            "search_regime_policy_version": 3,
            "trusted_win_total": 0,
            "sealed_exact_audit": sealed,
        }
        regime = flow_module._replay_search_regime(
            [*rounds, summary],
            rounds_root=rounds_root,
            policy_version=3,
            max_rounds=MAX_ROUNDS,
        )
        summary["search_regime"] = copy.deepcopy(regime)
        rounds.append(summary)

    assert regime["status"] == "representation_change_required"
    assert regime["reason"] == "round_budget_exhausted_after_family_expansion"
    return rounds, regime


def _install_committed_handoff(
    tmp_path: Path,
    *,
    configured_max_rounds: int = MAX_ROUNDS,
) -> tuple[FlowConfig, HumanizeFlow, dict[str, Any]]:
    repo = tmp_path / "repo"
    repo.mkdir()
    config = FlowConfig(
        repo_dir=repo,
        run_id=RUN_ID,
        max_rounds=configured_max_rounds,
        milp_top=0,
        search_representation_id="css-bb-policy-v3-test",
        search_regime_policy_version=3,
        stop_on_representation_change=True,
    )
    flow = HumanizeFlow(config, reviewer=object())
    state = flow.store.initialize(config.serializable())
    rounds, regime = _sealed_round_history(flow.store.root / "rounds")
    state.update({
        "status": "search-complete",
        "current_round": MAX_ROUNDS,
        "rounds": rounds,
        "search_regime": copy.deepcopy(regime),
        "search_handoff_reason": "representation_change_required",
        "search_handoff_at_round": MAX_ROUNDS,
        "trusted_win_count": 0,
        "unresolved_candidates": {},
    })
    flow.store.write_state(state)
    return config, flow, state


def _resumed_flow(
    config: FlowConfig,
    *,
    starts: list[int],
) -> HumanizeFlow:
    def forbidden_evolution(*_args: Any, **_kwargs: Any) -> None:
        starts.append(MAX_ROUNDS + 1)
        raise AssertionError("a committed policy-v3 handoff started round 13")

    return HumanizeFlow(
        config,
        reviewer=object(),
        evolution_runner=forbidden_evolution,
    )


def test_round12_committed_handoff_resume_never_starts_round13(
    tmp_path: Path,
    sealed_exact_classifier: None,
) -> None:
    config, initial, _state = _install_committed_handoff(tmp_path)
    starts: list[int] = []

    # Reconstruct the flow as if the original process died immediately after
    # the atomic state commit but before its outer Stage-1 caller observed it.
    resumed = _resumed_flow(config, starts=starts)
    completed = resumed.run()

    assert completed["status"] == "search-complete"
    assert completed["current_round"] == MAX_ROUNDS
    assert completed["search_handoff_reason"] == (
        "representation_change_required"
    )
    assert completed["search_handoff_at_round"] == MAX_ROUNDS
    assert "pending_round" not in completed
    assert "round_phase" not in completed
    assert starts == []
    assert not initial.store.root.joinpath("rounds", "round-013").exists()


def test_policy_v3_round_budget_cannot_be_extended_under_same_run_id(
    tmp_path: Path,
    sealed_exact_classifier: None,
) -> None:
    config, initial, _state = _install_committed_handoff(tmp_path)
    extended = replace(config, max_rounds=MAX_ROUNDS + 1)
    durable_before = initial.store.state_path.read_bytes()

    with pytest.raises(ValueError, match="different configuration"):
        _resumed_flow(extended, starts=[]).run()

    assert initial.store.state_path.read_bytes() == durable_before
    assert FiveStagePipeline._is_monotonic_round_extension(
        {
            "mode": "humanize-flow",
            "flow_config": config.serializable(),
        },
        {
            "mode": "humanize-flow",
            "flow_config": extended.serializable(),
        },
    ) is False

    # Preserve the historical extension lane for policies whose replay does
    # not bind max_rounds into terminal machine evidence.
    v2_previous = replace(
        config,
        search_regime_policy_version=2,
        max_rounds=MAX_ROUNDS,
    ).serializable()
    v2_current = {**v2_previous, "max_rounds": MAX_ROUNDS + 1}
    assert FiveStagePipeline._is_monotonic_round_extension(
        {"mode": "humanize-flow", "flow_config": v2_previous},
        {"mode": "humanize-flow", "flow_config": v2_current},
    ) is True


@pytest.mark.parametrize(
    ("corruption", "message"),
    [
        ("max_rounds", "persisted round search regime disagrees"),
        ("marker", "search handoff round is invalid"),
        ("trusted_win", "search handoff cannot coexist with a trusted win"),
    ],
)
def test_round12_handoff_recovery_rejects_bound_state_tampering(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
    sealed_exact_classifier: None,
    corruption: str,
    message: str,
) -> None:
    config, initial, state = _install_committed_handoff(tmp_path)
    if corruption == "max_rounds":
        # An attacker cannot turn the terminal 12-round policy identity into a
        # 13-round search and thereby continue past the committed handoff.
        config = replace(config, max_rounds=MAX_ROUNDS + 1)
        state["config"] = config.serializable()
    elif corruption == "marker":
        state["search_handoff_at_round"] = MAX_ROUNDS - 1
    else:
        # Recovery must reject a marker if the independently rebuilt canonical
        # audit view now contains a trusted WIN, even when the sealed round
        # history still records the original no-WIN transition.
        state["trusted_win_count"] = 1
    initial.store.write_state(state)

    starts: list[int] = []
    resumed = _resumed_flow(config, starts=starts)
    if corruption == "trusted_win":
        monkeypatch.setattr(
            resumed,
            "_trusted_exact_audit_view",
            lambda _rows: ([], [{}]),
        )
    with pytest.raises(RoundTransactionError, match=message):
        resumed.run()

    assert starts == []
    assert not initial.store.root.joinpath("rounds", "round-013").exists()
