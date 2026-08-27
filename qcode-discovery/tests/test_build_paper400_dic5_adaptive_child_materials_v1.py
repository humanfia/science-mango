from __future__ import annotations

import contextlib
import hashlib
import json
import os
import tempfile
from pathlib import Path
from types import SimpleNamespace

import pytest

from scripts import build_paper400_dic5_adaptive_child_materials_v1 as materials


def _write_json(path: Path, value: object) -> None:
    path.parent.mkdir(mode=0o700, parents=True, exist_ok=True)
    path.write_bytes(materials._canonical_bytes(value) + b'\n')
    path.chmod(0o600)


def _sha(label: str) -> str:
    return hashlib.sha256(label.encode('ascii')).hexdigest()
def _refresh_observation_bundle(fixture: dict[str, object]) -> None:
    receipt_path = Path(fixture['receipt_path'])
    elapsed_path = Path(fixture['elapsed_path'])
    receipt = materials._read_json(receipt_path)
    elapsed_payload = elapsed_path.read_bytes()
    elapsed = json.loads(elapsed_payload)
    receipt_payload = receipt_path.read_bytes()
    files = {
        'measurement-receipt.json': receipt_payload,
        'elapsed-seconds-by-lane.json': elapsed_payload,
    }
    commit = materials._seal({
        'schema_version': 1,
        'kind': materials.OBSERVATION_BUNDLE_KIND,
        'authority': materials.AUTHORITY,
        'observation_root': str(receipt_path.parent),
        'batch_root': str(fixture['root']),
        'batch_manifest_sha256': fixture['batch_pin'],
        'observation_action_sequence': 5,
        'observation_action_result_sha256': (
            fixture['observation_result_pin']
        ),
        'observation_lane_outcome_sha256s': [
            lane['record_sha256'] for lane in fixture['observation_lanes']
        ],
        'measurement_receipt_sha256': receipt['record_sha256'],
        'elapsed_seconds_json_sha256': hashlib.sha256(
            elapsed_payload
        ).hexdigest(),
        'timeout_seconds': 86400.0,
        'elapsed_seconds_by_lane': elapsed,
        'files': [
            materials._file_record(
                relative,
                'operator_measurement_receipt'
                if relative == 'measurement-receipt.json'
                else 'exact_elapsed_float_array',
                payload,
            )
            for relative, payload in sorted(files.items())
        ],
        'source_binding': {'synthetic_test_fixture': True},
        'claim_scope': {'synthetic_test_fixture': True},
        'authenticated': False,
        'launch_authorized': False,
        'scientific_claim': False,
    })
    _write_json(receipt_path.parent / 'COMMIT.json', commit)
    fixture['observation_commit'] = commit



def _fixture(tmp_path: Path) -> dict[str, object]:
    tmp_path.chmod(0o700)
    root = tmp_path / 'old'
    root.mkdir(mode=0o700)
    batch_pin = _sha('batch')
    observation_claim_pin = _sha('observation-claim')
    observation_result_pin = _sha('observation-result')
    stop_claim_pin = _sha('stop-claim')
    stop_result_pin = _sha('stop-result')
    source_pin = _sha('v3')
    source_v2_pin = _sha('v2')
    batch = {'record_sha256': batch_pin}
    clock_ticks = os.sysconf('SC_CLK_TCK')
    proc_uptime = materials._parse_decimal_text('2000', 'test uptime')
    boottime = materials._parse_decimal_text('2000', 'test boottime')
    observation_lanes = []
    stopped_lanes = []
    receipt_lanes = []
    elapsed = []
    for lane in range(4):
        start_ticks = (1000 + lane) * clock_ticks
        active_pin = _sha(f'active-{lane}')
        session_pin = _sha(f'session-{lane}')
        observation_lane_pin = _sha(f'observation-lane-{lane}')
        observed = materials._generation_elapsed_upper_bound(
            boottime, start_ticks, clock_ticks,
        )
        conservative = float(int(observed.to_integral_value(
            rounding=materials.decimal.ROUND_CEILING,
        )))
        elapsed.append(conservative)
        observation_lanes.append({
            'lane_index': lane, 'global_leaf_index': lane * 64,
            'action_sequence': 5, 'action': 'resume',
            'claim_sha256': observation_claim_pin,
            'transport_state_after': 'RUNNING',
            'child_result_state': 'RUNNING', 'success': True,
            'goal_satisfied': True, 'terminal_claimed_after': False,
            'terminal_committed_after': False,
            'record_sha256': observation_lane_pin,
            'child_result': {
                'kind': 'paper400-nested-width10-resume-admission-v1',
                'root': str(root / 'lanes' / f'lane-{lane}'),
                'generation': 2, 'session_sha256': session_pin,
                'resume_manifest_sha256': active_pin,
            },
        })
        stopped_lanes.append({
            'lane_index': lane, 'global_leaf_index': lane * 64,
            'action_sequence': 6, 'action': 'checkpoint-stop',
            'claim_sha256': stop_claim_pin,
            'transport_state_after': 'CHECKPOINTED',
            'child_result_state': 'CHECKPOINTED', 'success': True,
            'goal_satisfied': True, 'terminal_claimed_after': False,
            'terminal_committed_after': False,
            'record_sha256': _sha(f'stopped-lane-{lane}'),
            'child_result': {
                'state': 'CHECKPOINTED',
                'generations': [{
                    'generation': 2,
                    'active_manifest_sha256': active_pin,
                    'pid': 1000 + lane,
                    'proc_start_ticks': start_ticks,
                    'pid_identity_alive': False,
                }],
            },
        })
        receipt_lanes.append({
            'lane_index': lane, 'global_leaf_index': lane * 64,
            'session_sha256': session_pin,
            'resume_lane_outcome_sha256': observation_lane_pin,
            'active_generation': 2, 'pid': 1000 + lane,
            'proc_start_ticks': start_ticks,
            'active_manifest_sha256': active_pin,
            'current_generation_elapsed_upper_bound_seconds_decimal': (
                materials._decimal_text(observed)
            ),
            'conservative_elapsed_seconds': conservative,
        })
    observation_result = {
        'action_sequence': 5, 'action': 'resume',
        'batch_manifest_sha256': batch_pin,
        'claim_sha256': observation_claim_pin,
        'lane_outcome_sha256s': [
            lane['record_sha256'] for lane in observation_lanes
        ],
        'all_lanes_succeeded': True,
        'all_lanes_goal_satisfied': True,
        'goal_satisfied_lane_count': 4,
        'action_history_complete': True,
        'record_sha256': observation_result_pin,
    }
    stop_claim = {
        'action_sequence': 6, 'action': 'checkpoint-stop',
        'batch_manifest_sha256': batch_pin,
        'previous_action_result_sha256': observation_result_pin,
        'record_sha256': stop_claim_pin,
    }
    stop_result = {
        'claim_sha256': stop_claim_pin,
        'previous_action_result_sha256': observation_result_pin,
        'lane_outcome_sha256s': [
            lane['record_sha256'] for lane in stopped_lanes
        ],
        'all_lanes_succeeded': True,
        'all_lanes_goal_satisfied': True,
        'goal_satisfied_lane_count': 4,
        'action_history_complete': True,
        'record_sha256': stop_result_pin,
    }
    _write_json(root / 'batch.json', batch)
    for lane, value in enumerate(observation_lanes):
        _write_json(root / f'actions/000005/lane-{lane}.json', value)
    _write_json(root / 'actions/000005/result.json', observation_result)
    _write_json(root / 'actions/000006/claim.json', stop_claim)
    for lane, value in enumerate(stopped_lanes):
        _write_json(root / f'actions/000006/lane-{lane}.json', value)
    _write_json(root / 'actions/000006/result.json', stop_result)
    parent = {'manifest_sha256': _sha('parent')}
    width6 = {'manifest_sha256': _sha('width6')}
    width10 = {'manifest_sha256': _sha('width10')}
    _write_json(root / 'static/parent-manifest.json', parent)
    _write_json(root / 'static/width6-campaign.json', width6)
    _write_json(root / 'static/width10-campaign.json', width10)
    observation_root = tmp_path / 'observation-input'
    observation_root.mkdir(mode=0o700)
    elapsed_path = observation_root / 'elapsed-seconds-by-lane.json'
    _write_json(elapsed_path, elapsed)
    receipt = materials._seal({
        'schema_version': 1, 'kind': materials.RECEIPT_KIND,
        'batch_root': str(root), 'batch_manifest_sha256': batch_pin,
        'observation_action_sequence': 5,
        'observation_action_result_sha256': observation_result_pin,
        'timeout_seconds': 86400.0,
        'elapsed_seconds_by_lane': elapsed,
        'elapsed_seconds_json_sha256': hashlib.sha256(
            elapsed_path.read_bytes()
        ).hexdigest(),
        'annotation_source': 'operator-annotation-not-solver-result-v2',
        'timed_out': False, 'hardness_only': True,
        'measurement_method': (
            'operator-current-generation-clock-boottime-plus-one-tick-'
            'conservative-ceil-v1'
        ),
        'boot_id_sha256': materials._boot_id_sha256(),
        'clock_ticks_per_second': clock_ticks,
        'proc_uptime_seconds_decimal': materials._decimal_text(proc_uptime),
        'clock_boottime_seconds_decimal': materials._decimal_text(boottime),
        'sample_utc_before': '2026-08-27T00:00:00.000000Z',
        'sample_utc_after': '2026-08-27T00:00:01.000000Z',
        'observer_source_sha256': hashlib.sha256(
            materials._BUILDER_SOURCE_PAYLOAD
        ).hexdigest(),
        'switch_v3_source_sha256': source_pin,
        'switch_v2_source_sha256': source_v2_pin,
        'lanes': receipt_lanes, 'authenticated': False,
        'launch_authorized': False, 'scientific_claim': False,
    })
    receipt_path = observation_root / 'measurement-receipt.json'
    _write_json(receipt_path, receipt)
    fixture = {
        'root': root, 'batch_pin': batch_pin,
        'observation_result_pin': observation_result_pin,
        'result_pin': stop_result_pin, 'elapsed': elapsed,
        'elapsed_path': elapsed_path, 'receipt': receipt,
        'receipt_path': receipt_path, 'parent': parent,
        'width6': width6, 'width10': width10,
        'observation_lanes': observation_lanes,
        'lanes': stopped_lanes, 'source_pin': source_pin,
        'source_v2_pin': source_v2_pin,
    }
    _refresh_observation_bundle(fixture)
    return fixture


class _FakeBase:
    _read_json = staticmethod(materials._read_json)


class _FakeSwitch:
    base = _FakeBase()

    def __init__(self, fixture: dict[str, object]) -> None:
        self.fixture = fixture

    def build_switch_evidence_record(self, root: Path, **kwargs: object) -> dict:
        assert root == self.fixture['root']
        assert kwargs == {
            'timeout_seconds': 86400.0,
            'elapsed_seconds_by_lane': self.fixture['elapsed'],
            'strict_base': True,
        }
        lanes = []
        for lane in range(4):
            hard = {
                'evidence_sha256': _sha(f'hard-{lane}'),
                'lane_index': lane,
            }
            lanes.append({
                'lane_index': lane, 'global_leaf_index': lane * 64,
                'cpu': (10, 11, 48, 57)[lane],
                'hard_evidence': hard,
                'hard_evidence_sha256': hard['evidence_sha256'],
            })
        return {
            'record_sha256': _sha('switch'),
            'batch_manifest_sha256': self.fixture['batch_pin'],
            'parent_manifest_sha256': self.fixture['parent'][
                'manifest_sha256'
            ],
            'width6_campaign_sha256': self.fixture['width6'][
                'manifest_sha256'
            ],
            'width10_campaign_sha256': self.fixture['width10'][
                'manifest_sha256'
            ],
            'action_history': {
                'checkpoint_stop_result_sha256': self.fixture['result_pin'],
                'completed_action_count': 7,
                'actions': [{
                    'sequence': index,
                    'result_sha256': (
                        self.fixture['observation_result_pin']
                        if index == 5 else self.fixture['result_pin']
                        if index == 6 else _sha(f'action-result-{index}')
                    ),
                    'lane_outcome_sha256s': (
                        [
                            value['record_sha256']
                            for value in self.fixture['observation_lanes']
                        ]
                        if index == 5 else [
                            value['record_sha256']
                            for value in self.fixture['lanes']
                        ]
                        if index == 6 else []
                    ),
                } for index in range(7)],
            },
            'lanes': lanes,
        }


class _FakeOverlay:
    width10 = SimpleNamespace(TARGET_PARENT_CUBE_INDEX=0)
    optimized = SimpleNamespace(build_optimized_instance=lambda: object())

    @contextlib.contextmanager
    def acquire_campaign_replay_token(self, *args: object, **kwargs: object):
        assert kwargs['strict_base'] is True
        yield object()

    def build_overlay_manifest(self, *args: object, **kwargs: object) -> dict:
        lane = kwargs['global_leaf_index'] // 64
        variable = kwargs['candidate_variables'][0]
        return {
            'manifest_sha256': _sha(f'overlay-{lane}-{variable}'),
            'candidate_policy': {'selected_variable': variable},
            'descendants': [
                {'descendant_sha256': _sha(f'desc-{lane}-0')},
                {'descendant_sha256': _sha(f'desc-{lane}-1')},
            ],
        }

    def verify_overlay_manifest(self, manifest: dict, *args: object, **kwargs: object) -> dict:
        del args, kwargs
        return {
            'valid': True, 'current_source_exact_replay': True,
            'launch_authorized': False,
            'record_sha256': _sha('verification-' + manifest['manifest_sha256']),
        }


def _invoke(
    monkeypatch: pytest.MonkeyPatch, fixture: dict[str, object],
    output: Path, *, publish: bool = True,
    refresh_observation: bool = True,
) -> dict:
    if refresh_observation:
        _refresh_observation_bundle(fixture)
    source_binding = materials._seal({
        'schema_version': 1, 'method': 'synthetic-exact-source-test',
        'sources': [],
    })
    monkeypatch.setattr(
        materials, '_load_exact_sources',
        lambda **kwargs: (
            _FakeSwitch(fixture), _FakeOverlay(), source_binding,
        ),
    )
    return materials.build_material_bundle(
        batch_root=fixture['root'], output_dir=output,
        measurement_receipt_path=fixture['receipt_path'],
        elapsed_seconds_by_lane_json=fixture['elapsed_path'],
        timeout_seconds=86400.0,
        candidate_variables=[17, 18, 19, 20],
        expected_batch_manifest_sha256=fixture['batch_pin'],
        expected_switch_v3_source_sha256=_sha('v3'),
        expected_switch_v2_source_sha256=_sha('v2'),
        expected_overlay_v2_source_sha256=_sha('overlay'),
        expected_adaptive_v2_source_sha256=_sha('adaptive'),
        publish=publish,
    )


def test_bundle_is_atomic_complete_and_has_canonical_eight_target_plan(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    fixture = _fixture(tmp_path)
    output = tmp_path / 'bundle'
    commit = _invoke(monkeypatch, fixture, output)
    observed = materials._read_json(output / 'COMMIT.json')
    assert observed == commit
    assert materials._selfhash_valid(observed)
    assert observed['observation_action_sequence'] == 5
    assert observed['observation_action_result_sha256'] == (
        fixture['observation_result_pin']
    )
    assert observed['observation_bundle_sha256'] == (
        fixture['observation_commit']['record_sha256']
    )
    assert observed['authenticated'] is False
    assert observed['launch_authorized'] is False
    assert observed['target_keys'] == [list(key) for key in materials.TARGET_KEYS]
    expected_cli_keys = {
        'batch_root', 'parent_manifest', 'width6_campaign',
        'width10_campaign', 'overlay_manifest', 'hard_evidence',
        'switch_evidence', 'elapsed_seconds_by_lane_json',
        'expected_overlay_sha256', 'expected_hard_evidence_sha256',
        'expected_switch_evidence_sha256',
        'expected_batch_manifest_sha256', 'descendant_index',
        'candidate_variable', 'timeout_seconds', 'proof_max_bytes',
    }
    plan = materials._read_json(output / 'prepare-plan.json')
    assert [entry['target_key'] for entry in plan['entries']] == [
        list(key) for key in materials.TARGET_KEYS
    ]
    assert [
        entry['postconditions']['expected_start_batch_cpu']
        for entry in plan['entries']
    ] == [10, 11, 48, 57, 10, 11, 48, 57]
    for entry in plan['entries']:
        cli = entry['v5_prepare_cli']
        assert cli['subcommand'] == 'prepare'
        assert cli['required_operator_cli_args'] == ['root']
        assert set(cli['provided_cli_args']) == expected_cli_keys
        assert 'expected_descendant_sha256' not in cli['provided_cli_args']
        assert 'cpu' not in cli['provided_cli_args']
        assert materials._is_sha256(
            entry['postconditions']['expected_descendant_sha256']
        )
    assert (output / 'elapsed-seconds-by-lane.json').read_bytes() == (
        fixture['elapsed_path'].read_bytes()
    )
    for record in observed['files']:
        payload = (output / record['relative_path']).read_bytes()
        assert hashlib.sha256(payload).hexdigest() == record['sha256']
        assert len(payload) == record['bytes']
        assert stat_mode(output / record['relative_path']) == 0o600
    with pytest.raises(materials.AdaptiveMaterialBuildError, match='already exists'):
        _invoke(monkeypatch, fixture, output)


def stat_mode(path: Path) -> int:
    return os.stat(path, follow_symlinks=False).st_mode & 0o777


def test_output_directory_reservation_race_is_uncommitted(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    fixture = _fixture(tmp_path)
    output = tmp_path / 'bundle-race'
    original_mkdir = materials.os.mkdir

    def racing_mkdir(path: Path, mode: int) -> None:
        if Path(path) == output:
            original_mkdir(path, 0o700)
        original_mkdir(path, mode)

    monkeypatch.setattr(materials.os, 'mkdir', racing_mkdir)
    with pytest.raises(
        materials.AdaptiveMaterialBuildError,
        match='raced into existence',
    ):
        _invoke(monkeypatch, fixture, output)
    assert output.is_dir()
    assert not (output / 'COMMIT.json').exists()


def test_midwrite_failure_never_publishes_target(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    fixture = _fixture(tmp_path)
    output = tmp_path / 'bundle-midwrite'
    original = materials._publish_new_file
    calls = 0

    def fail_third(path: Path, payload: bytes) -> None:
        nonlocal calls
        calls += 1
        if calls == 3:
            raise OSError('injected midwrite')
        original(path, payload)

    monkeypatch.setattr(materials, '_publish_new_file', fail_third)
    with pytest.raises(OSError, match='injected midwrite'):
        _invoke(monkeypatch, fixture, output)
    assert output.is_dir()
    assert not (output / 'COMMIT.json').exists()


def test_receipt_requires_exact_float_file_and_conservative_ceil(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    fixture = _fixture(tmp_path)
    bad = dict(fixture['receipt'])
    bad_lanes = [dict(item) for item in bad['lanes']]
    bad_lanes[0]['conservative_elapsed_seconds'] = 100.0
    bad['lanes'] = bad_lanes
    bad.pop('record_sha256')
    bad = materials._seal(bad)
    _write_json(fixture['receipt_path'], bad)
    with pytest.raises(
        materials.AdaptiveMaterialBuildError,
        match='reproducible conservative ceil|lane/elapsed file mismatch',
    ):
        _invoke(monkeypatch, fixture, tmp_path / 'bad-receipt', publish=False)
    _write_json(fixture['receipt_path'], fixture['receipt'])
    fixture['elapsed_path'].write_bytes(b'[101,202.0,303.0,404.0]\n')
    with pytest.raises(
        materials.AdaptiveMaterialBuildError, match='exact integer floats',
    ):
        _invoke(monkeypatch, fixture, tmp_path / 'bad-elapsed', publish=False)


def test_receipt_session_must_match_resume_and_checkpointed_generation(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    fixture = _fixture(tmp_path)
    bad = dict(fixture['receipt'])
    lanes = [dict(item) for item in bad['lanes']]
    lanes[1]['session_sha256'] = _sha('substituted-session')
    bad['lanes'] = lanes
    bad.pop('record_sha256')
    _write_json(fixture['receipt_path'], materials._seal(bad))
    with pytest.raises(
        materials.AdaptiveMaterialBuildError,
        match='misses action000005/stopped process identity',
    ):
        _invoke(monkeypatch, fixture, tmp_path / 'bad-process', publish=False)


def test_action_000006_lane_hash_binding_is_fail_closed(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    fixture = _fixture(tmp_path)
    lane = dict(fixture['lanes'][2])
    lane['goal_satisfied'] = False
    _write_json(fixture['root'] / 'actions/000006/lane-2.json', lane)
    with pytest.raises(
        materials.AdaptiveMaterialBuildError,
        match='old actions 000005/000006 binding mismatch',
    ):
        _invoke(monkeypatch, fixture, tmp_path / 'bad-action', publish=False)


def test_exact_loader_binds_current_v3_v2_overlay_and_adaptive_sources() -> None:
    pins = {
        'expected_switch_v3_sha256': hashlib.sha256(
            (materials.PROJECT / materials.SWITCH_V3_RELATIVE).read_bytes()
        ).hexdigest(),
        'expected_switch_v2_sha256': hashlib.sha256(
            (materials.PROJECT / materials.SWITCH_V2_RELATIVE).read_bytes()
        ).hexdigest(),
        'expected_overlay_v2_sha256': hashlib.sha256(
            (materials.PROJECT / materials.OVERLAY_V2_RELATIVE).read_bytes()
        ).hexdigest(),
        'expected_adaptive_v2_sha256': hashlib.sha256(
            (
                materials.PROJECT
                / 'investigations/paper400_dic5_adaptive_cnc_v2.py'
            ).read_bytes()
        ).hexdigest(),
    }
    switch, overlay, binding = materials._load_exact_sources(**pins)
    assert switch.TARGET_KEYS == materials.TARGET_KEYS
    assert overlay.adaptive.__name__ == materials.ADAPTIVE_V2_MODULE
    assert binding['method'] == 'externally-pinned-exact-source-execution-v1'
    assert [record['sha256'] for record in binding['sources']] == list(
        pins.values()
    )
    with pytest.raises(
        materials.AdaptiveMaterialBuildError, match='switch-v3 source pin',
    ):
        materials._load_exact_sources(
            **{**pins, 'expected_switch_v3_sha256': _sha('wrong')}
        )
    compile_called = False

    def forbidden_compile(*args: object, **kwargs: object):
        nonlocal compile_called
        compile_called = True
        raise AssertionError('source execution occurred before switch-v2 pin check')

    with pytest.MonkeyPatch.context() as local_patch:
        local_patch.setattr(
            materials, 'compile', forbidden_compile, raising=False,
        )
        with pytest.raises(
            materials.AdaptiveMaterialBuildError,
            match='switch-v2 source pin mismatch before exec',
        ):
            materials._load_exact_sources(
                **{**pins, 'expected_switch_v2_sha256': _sha('wrong-v2')}
            )
    assert compile_called is False

def test_observe_running_batch_publishes_operator_receipt_and_releases_locks(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    fixture = _fixture(tmp_path)
    switch_pin = hashlib.sha256(
        (materials.PROJECT / materials.SWITCH_V3_RELATIVE).read_bytes()
    ).hexdigest()
    held_locks = []

    class Held:
        closed = False

        def close(self) -> None:
            self.closed = True

    class Base:
        def _acquire_all_locks(self, root: Path):
            assert root == fixture['root']
            held_locks.extend(Held() for _ in range(9))
            return held_locks, []

        def _discover_sources(self, root: Path, **kwargs: object) -> dict:
            assert root == fixture['root']
            assert kwargs == {
                'expected_batch_manifest_sha256': fixture['batch_pin'],
            }
            return {'fresh': True}

        def _load_exact_modules(self, discovery: dict):
            assert discovery == {'fresh': True}
            return object(), object(), []

    switch = SimpleNamespace(base=Base())
    audit_keys = (
        'lane_index', 'global_leaf_index', 'session_sha256',
        'resume_lane_outcome_sha256', 'active_generation', 'pid',
        'proc_start_ticks', 'active_manifest_sha256',
    )
    audit_lanes = [
        {key: lane[key] for key in audit_keys}
        for lane in fixture['receipt']['lanes']
    ]
    running = {
        'manifest': {'record_sha256': fixture['batch_pin']},
        'observation_result': {
            'record_sha256': fixture['observation_result_pin'],
        },
        'observation_lanes': fixture['observation_lanes'],
        'lanes': audit_lanes,
    }
    contexts = [{'lane_index': lane} for lane in range(4)]
    sampled = {
        'sample_utc_before': '2026-08-27T00:00:00.000000Z',
        'sample_utc_after': '2026-08-27T00:00:00.000001Z',
        'boot_id_sha256': materials._boot_id_sha256(),
        'clock_ticks_per_second': os.sysconf('SC_CLK_TCK'),
        'proc_uptime_seconds_decimal': (
            fixture['receipt']['proc_uptime_seconds_decimal']
        ),
        'clock_boottime_seconds_decimal': (
            fixture['receipt']['clock_boottime_seconds_decimal']
        ),
        'elapsed_seconds_by_lane': fixture['elapsed'],
        'lanes': [dict(lane) for lane in fixture['receipt']['lanes']],
        'proc_identities': [
            {
                'pid': lane['pid'], 'state': 'S',
                'proc_start_ticks': lane['proc_start_ticks'],
            }
            for lane in audit_lanes
        ],
    }
    reverified = []
    switch_v2_pin = hashlib.sha256(
        (materials.PROJECT / materials.SWITCH_V2_RELATIVE).read_bytes()
    ).hexdigest()
    monkeypatch.setattr(
        materials, '_load_exact_switch_v3',
        lambda expected, expected_v2: (
            switch,
            {
                'role': 'adaptive_switch_evidence_v3_source',
                'sha256': expected,
            },
            {
                'role': 'adaptive_switch_evidence_v2_primitives_source',
                'sha256': expected_v2,
            },
        ),
    )
    monkeypatch.setattr(
        materials, '_running_snapshot_locked',
        lambda root, coordinator, child: (running, contexts),
    )
    monkeypatch.setattr(
        materials, '_sample_running_processes',
        lambda lanes: sampled if lanes == audit_lanes else None,
    )
    monkeypatch.setattr(
        materials, '_reverify_running_snapshot',
        lambda child, observed_contexts, value: reverified.append(
            (observed_contexts, value)
        ),
    )
    output = tmp_path / 'observation'
    commit = materials.observe_running_batch(
        batch_root=fixture['root'], output_dir=output,
        timeout_seconds=86400.0,
        expected_batch_manifest_sha256=fixture['batch_pin'],
        expected_switch_v3_source_sha256=switch_pin,
        expected_switch_v2_source_sha256=switch_v2_pin,
    )
    receipt = materials._read_json(output / 'measurement-receipt.json')
    assert materials._read_json(output / 'COMMIT.json') == commit
    assert receipt['annotation_source'] == (
        'operator-annotation-not-solver-result-v2'
    )
    assert receipt['timed_out'] is False
    assert receipt['scientific_claim'] is False
    assert commit['claim_scope'] == {
        'current_active_generation_age_only': True,
        'cumulative_solver_elapsed_claimed': False,
        'solver_native_timing_claimed': False,
        'timeout_claimed': False,
        'scientific_certificate': False,
    }
    assert reverified == [(contexts, sampled)]
    assert len(held_locks) == 9 and all(lock.closed for lock in held_locks)
    assert stat_mode(output) == 0o700
    assert all(
        stat_mode(output / record['relative_path']) == 0o600
        for record in commit['files']
    )
    assert stat_mode(output / 'COMMIT.json') == 0o600


def test_running_observation_rejects_pid_start_ticks_race(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    clock_ticks = os.sysconf('SC_CLK_TCK')
    expected = [
        {'pid': 9000 + lane, 'proc_start_ticks': (100 + lane) * clock_ticks}
        for lane in range(4)
    ]
    calls = 0

    def identity(pid: int) -> dict:
        nonlocal calls
        lane = calls % 4
        round_index = calls // 4
        calls += 1
        assert pid == expected[lane]['pid']
        ticks = expected[lane]['proc_start_ticks']
        if round_index == 1 and lane == 0:
            ticks += 1
        return {'pid': pid, 'state': 'S', 'proc_start_ticks': ticks}

    monkeypatch.setattr(materials, '_proc_stat_identity', identity)
    monkeypatch.setattr(
        materials, '_proc_uptime',
        lambda: materials.decimal.Decimal('1000'),
    )
    monkeypatch.setattr(
        materials, '_clock_boottime',
        lambda: materials.decimal.Decimal('1000'),
    )
    monkeypatch.setattr(materials, '_boot_id_sha256', lambda: _sha('boot'))
    monkeypatch.setattr(
        materials, '_utc_now',
        lambda: '2026-08-27T00:00:00.000000Z',
    )
    with pytest.raises(
        materials.AdaptiveMaterialBuildError,
        match='identity changed during observation',
    ):
        materials._sample_running_processes(expected)


def test_root_parent_rejected_and_real_nfs_publish_is_noreplace_and_mode_exact(
) -> None:
    root_info = Path('/root').stat()
    if (
        root_info.st_uid == os.geteuid()
        and stat_mode(Path('/root')) == 0o700
    ):
        pytest.skip('/root happens to satisfy the trusted-parent policy')
    with pytest.raises(
        materials.AdaptiveMaterialBuildError,
        match='owned canonical mode-0700',
    ):
        materials._new_bundle_path(
            Path('/root') / f'forbidden-builder-output-{os.getpid()}'
        )

    nfs_parent = Path('/root/paper400-v5-nfs-preflight-final-20260827')
    if not nfs_parent.is_dir():
        pytest.skip('designated real NFS preflight directory is absent')
    info = nfs_parent.stat()
    if info.st_uid != os.geteuid() or stat_mode(nfs_parent) != 0o700:
        pytest.skip('designated real NFS preflight directory is not trusted')
    with tempfile.TemporaryDirectory(
        prefix='builder-material-test-', dir=nfs_parent,
    ) as raw:
        scratch = Path(raw)
        scratch.chmod(0o700)
        payload = materials._json_payload({'nfs': 'real-scratch'})
        files = {'payload.json': payload}
        commit = materials._seal({
            'schema_version': 1,
            'kind': 'paper400-builder-real-nfs-test-v1',
            'files': [
                materials._file_record(
                    'payload.json', 'real_nfs_test_payload', payload,
                ),
            ],
        })
        target = scratch / 'published'
        previous_umask = os.umask(0o777)
        try:
            materials._publish_bundle(target, files, commit)
        finally:
            os.umask(previous_umask)
        materials._verify_published_bundle(target, commit)
        assert stat_mode(target) == 0o700
        assert stat_mode(target / 'payload.json') == 0o600
        assert stat_mode(target / 'COMMIT.json') == 0o600
        with pytest.raises(FileExistsError):
            os.mkdir(target, 0o700)
        with pytest.raises(
            materials.AdaptiveMaterialBuildError,
            match='already exists',
        ):
            materials._publish_bundle(target, files, commit)
        materials._verify_published_bundle(target, commit)


def test_build_rejects_receipt_without_observation_commit(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    fixture = _fixture(tmp_path)
    commit_path = Path(fixture['receipt_path']).parent / 'COMMIT.json'
    commit_path.unlink()
    with pytest.raises(
        materials.AdaptiveMaterialBuildError,
        match='cannot resolve.*COMMIT',
    ):
        _invoke(
            monkeypatch, fixture, tmp_path / 'missing-observation-commit',
            publish=False, refresh_observation=False,
        )


def test_proc_uptime_fixed_two_decimal_and_one_tick_upper_bound() -> None:
    assert materials._parse_proc_uptime_payload(
        b'1.20 1.00\n'
    ) == materials.decimal.Decimal('1.20')
    assert materials._parse_proc_uptime_payload(
        b'1.00 0.00\n'
    ) == materials.decimal.Decimal('1.00')
    with pytest.raises(
        materials.AdaptiveMaterialBuildError,
        match='fixed-two-decimal',
    ):
        materials._parse_proc_uptime_payload(b'1.2 1.00\n')
    clock_ticks = os.sysconf('SC_CLK_TCK')
    assert materials._generation_elapsed_upper_bound(
        materials.decimal.Decimal('10'), 9 * clock_ticks, clock_ticks,
    ) == materials.decimal.Decimal(1) + (
        materials.decimal.Decimal(1) / materials.decimal.Decimal(clock_ticks)
    )
