from __future__ import annotations

import contextlib
import hashlib
import json
import os
import resource
import signal
import subprocess
import sys
import time
import types
from pathlib import Path
from types import SimpleNamespace
from typing import Any, Iterator, Mapping

import pytest


PROJECT = Path(__file__).resolve().parent.parent
FINAL_RELATIVE = Path('scripts/run_paper400_dic5_adaptive_child_resume_v5.py')
DRAFT = PROJECT / FINAL_RELATIVE


def _load_draft() -> Any:
    name = 'scripts.run_paper400_dic5_adaptive_child_resume_v5'
    module = types.ModuleType(name)
    module.__file__ = str(PROJECT / FINAL_RELATIVE)
    module.__package__ = 'scripts'
    module.__loader__ = None
    module.__spec__ = None
    sys.modules[name] = module
    payload = DRAFT.read_bytes()
    exec(compile(payload, module.__file__, 'exec', dont_inherit=True), module.__dict__)
    return module


runner = _load_draft()
controller = runner.controller

PARENT_DIMACS = (
    b'c tiny UNSAT without unit propagation\n'
    b'p cnf 3 4\n'
    b'2 3 0\n2 -3 0\n-2 3 0\n-2 -3 0\n'
)
BATCH_PIN = 'b' * 64
CAPS = {'proof_max_bytes': 64 << 20}
TEST_INSTANCE = object()
PARENT_PIN = WIDTH6_PIN = WIDTH10_PIN = '0' * 64


def _seal_field(value: Mapping[str, Any], field: str) -> dict[str, Any]:
    result = dict(value)
    result[field] = runner.canonical_sha256(result)
    return result


def _parse_dimacs(payload: bytes) -> dict[str, Any]:
    variables = clauses_expected = None
    clauses: list[list[int]] = []
    for raw in payload.decode('ascii').splitlines():
        line = raw.strip()
        if not line or line.startswith('c'):
            continue
        if line.startswith('p '):
            _, _, raw_variables, raw_clauses = line.split()
            variables, clauses_expected = int(raw_variables), int(raw_clauses)
            continue
        values = [int(item) for item in line.split()]
        assert values[-1] == 0
        clauses.append(values[:-1])
    assert variables is not None and clauses_expected == len(clauses)
    return {'num_variables': variables, 'num_clauses': len(clauses), 'clauses': clauses}


def _render(parent: bytes, assumptions: list[int]) -> bytes:
    rendered: list[str] = []
    for line in parent.decode('ascii').splitlines():
        if line.startswith('p cnf '):
            parts = line.split()
            rendered.append(f'p cnf {parts[2]} {int(parts[3]) + len(assumptions)}')
        else:
            rendered.append(line)
    rendered.extend(f'{literal} 0' for literal in assumptions)
    return ('\n'.join(rendered) + '\n').encode('ascii')


def _structured_hash(*, num_variables: int, clauses: list[list[int]], native_atmost: Any) -> str:
    assert native_atmost is None
    return runner.canonical_sha256({
        'num_variables': num_variables, 'clauses': clauses, 'native_atmost': None,
    })


class _FakeAdaptive:
    render_cube_dimacs = staticmethod(_render)
    parse_dimacs = staticmethod(_parse_dimacs)


class _FakeCube16:
    _cnf_sha256 = staticmethod(_structured_hash)


class _FakeWidth10:
    TARGET_PARENT_CUBE_INDEX = 0
    cube16 = SimpleNamespace(optimized=SimpleNamespace(build_optimized_instance=lambda: TEST_INSTANCE))

    @staticmethod
    def verify_campaign_manifest(
        width10: Mapping[str, Any], width6: Mapping[str, Any],
        parent: Mapping[str, Any], instance: Any, **kwargs: Any,
    ) -> dict[str, Any]:
        assert instance is TEST_INSTANCE and kwargs['strict_base'] is False
        assert width10['manifest_sha256'] == WIDTH10_PIN
        assert width6['manifest_sha256'] == WIDTH6_PIN
        assert parent['manifest_sha256'] == PARENT_PIN
        return {
            'valid': True, 'mutually_exclusive': True, 'exhaustive': True,
            'parent000_formula_equivalence_certified': True,
            'record_sha256': 'c' * 64,
        }

    @staticmethod
    def verified_child_dimacs_from_verification(*args: Any, **kwargs: Any) -> bytes:
        assert kwargs['global_leaf_index'] == 0 and kwargs['strict_base'] is False
        return PARENT_DIMACS


class _FakeOverlay:
    width10 = _FakeWidth10
    adaptive = _FakeAdaptive
    cube16 = _FakeCube16

    @staticmethod
    def verify_overlay_manifest(
        manifest: Mapping[str, Any], width10: Mapping[str, Any],
        width6: Mapping[str, Any], parent: Mapping[str, Any], instance: Any,
        **kwargs: Any,
    ) -> dict[str, Any]:
        assert instance is TEST_INSTANCE and kwargs['strict_base'] is False
        assert kwargs['candidate_variables'] == [1]
        return {
            'valid': True, 'current_source_exact_replay': True,
            'record_sha256': 'd' * 64,
        }


SCIENCE = (_FakeOverlay, _FakeWidth10, _FakeAdaptive, _FakeCube16)

class _ScopedFakeOverlay(_FakeOverlay):
    full_replays = 0
    local_replays = 0
    last_token: Any = None

    canonical_bytes = staticmethod(runner.canonical_bytes)

    @staticmethod
    def selfhash_valid(value: Any, field: str = 'record_sha256') -> bool:
        if type(value) is not dict or type(value.get(field)) is not str:
            return False
        unsigned = dict(value)
        stored = unsigned.pop(field)
        return stored == runner.canonical_sha256(unsigned)

    @staticmethod
    @contextlib.contextmanager
    def acquire_campaign_replay_token(
        width10: Mapping[str, Any], width6: Mapping[str, Any],
        parent: Mapping[str, Any], instance: Any, **kwargs: Any,
    ) -> Iterator[Any]:
        _ScopedFakeOverlay.full_replays += 1
        raw = _FakeWidth10.verify_campaign_manifest(
            width10, width6, parent, instance,
            strict_base=kwargs['strict_base'],
        )
        unsigned = dict(raw)
        unsigned.pop('record_sha256')
        token = SimpleNamespace(
            active=True, width10=width10, width6=width6, parent=parent,
            instance=instance, strict_base=kwargs['strict_base'],
            verification=runner.seal(unsigned),
        )
        _ScopedFakeOverlay.last_token = token
        try:
            yield token
        finally:
            token.active = False

    @staticmethod
    def _campaign_replay_verification(
        token: Any, width10: Mapping[str, Any], width6: Mapping[str, Any],
        parent: Mapping[str, Any], instance: Any, **kwargs: Any,
    ) -> dict[str, Any]:
        assert token.active is True
        assert token.width10 is width10 and token.width6 is width6
        assert token.parent is parent and token.instance is instance
        assert token.strict_base is kwargs['strict_base']
        return dict(token.verification)

    @staticmethod
    def verify_overlay_manifest(
        manifest: Mapping[str, Any], width10: Mapping[str, Any],
        width6: Mapping[str, Any], parent: Mapping[str, Any],
        instance: Any, **kwargs: Any,
    ) -> dict[str, Any]:
        token = kwargs.pop('_campaign_replay_token')
        _ScopedFakeOverlay._campaign_replay_verification(
            token, width10, width6, parent, instance,
            strict_base=kwargs['strict_base'],
        )
        _FakeOverlay.verify_overlay_manifest(
            manifest, width10, width6, parent, instance, **kwargs,
        )
        _ScopedFakeOverlay.local_replays += 1
        return runner.seal({
            'valid': True, 'current_source_exact_replay': True,
        })


SCOPED_SCIENCE = (_ScopedFakeOverlay, _FakeWidth10, _FakeAdaptive, _FakeCube16)


def _materials() -> dict[str, Any]:
    global PARENT_PIN, WIDTH6_PIN, WIDTH10_PIN
    parent = _seal_field({'kind': 'fake-parent'}, 'manifest_sha256')
    width6 = _seal_field({'kind': 'fake-width6'}, 'manifest_sha256')
    width10 = _seal_field({'kind': 'fake-width10'}, 'manifest_sha256')
    PARENT_PIN, WIDTH6_PIN, WIDTH10_PIN = (
        parent['manifest_sha256'], width6['manifest_sha256'], width10['manifest_sha256'],
    )
    descendants: list[dict[str, Any]] = []
    for index, literal in enumerate((1, -1)):
        payload = _render(PARENT_DIMACS, [literal])
        parsed = _parse_dimacs(payload)
        descendants.append(_seal_field({
            'descendant_index': index, 'adaptive_node_id': f'node-{index}',
            'relative_assignment_literals': [literal], 'pending': True,
            'observed_status': 'PENDING', 'status_source': 'generated-frontier-v1',
            'solver_terminal_authenticated': False,
            'child_cnf_sha256': _structured_hash(
                num_variables=parsed['num_variables'], clauses=parsed['clauses'], native_atmost=None,
            ),
            'child_dimacs_sha256': hashlib.sha256(payload).hexdigest(),
            'child_num_variables': parsed['num_variables'],
            'child_num_clauses': parsed['num_clauses'],
            'child_dimacs_bytes': len(payload),
        }, 'descendant_sha256'))
    overlay = _seal_field({
        'kind': 'fake-adaptive-overlay', 'test_only': True,
        'launch_authorized': False,
        'parent_scope': {
            'global_leaf_index': 0,
            'verified_child_payload_sha256': hashlib.sha256(PARENT_DIMACS).hexdigest(),
            'verified_child_payload_bytes': len(PARENT_DIMACS),
        },
        'descendants': descendants,
    }, 'manifest_sha256')
    hard = _seal_field({'kind': 'fake-hard-evidence'}, 'evidence_sha256')
    switch = runner.seal({'kind': 'fake-switch-evidence'})
    return {
        'parent': parent, 'width6': width6, 'width10': width10,
        'overlay': overlay, 'hard': hard, 'switch': switch,
    }


def _switch_verifier(record: Mapping[str, Any]) -> dict[str, Any]:
    assert runner.selfhash_valid(record)
    return {
        'valid': True, 'authenticated': False, 'launch_authorized': False,
        'production_eligible': False, 'scientific_claim': False,
    }


def _fake_source_binding() -> dict[str, Any]:
    value = {
        'method': 'synthetic-test-source-binding-v1',
        'sources': {
            'adaptive_child_runner_v5_source': {
                'role': 'adaptive_child_runner_v5_source',
                'relative_path': FINAL_RELATIVE.as_posix(),
                'sha256': '7' * 64, 'bytes': 1, 'links': 1, 'uid': os.geteuid(),
            },
        },
    }
    value['source_binding_sha256'] = runner.canonical_sha256(value)
    return value


def _fake_toolchain(paths: Mapping[str, Path], hashes: Mapping[str, str]) -> dict[str, Any]:
    tools = {
        role: {
            'role': role, 'path': str(Path(paths[role]).resolve(strict=True)),
            'sha256': hashes[role], 'bytes': 1, 'links': 1, 'uid': os.geteuid(),
        }
        for role in runner.TOOL_ROLES
    }
    value = {
        'method': 'synthetic-test-toolchain-v1', 'cadical_version': '1.9.5',
        'tools': tools, 'dmtcp': {'prefix': str(runner.DMTCP_PREFIX)},
        'runtime_libraries': [],
        'proof_format': 'binary-drat+converted-ascii-lrat-v1',
    }
    value['toolchain_sha256'] = runner.canonical_sha256(value)
    return value


@pytest.fixture(autouse=True)
def _synthetic_bindings(monkeypatch: pytest.MonkeyPatch) -> None:
    monkeypatch.setattr(runner, '_source_binding', _fake_source_binding)
    monkeypatch.setattr(runner, '_toolchain_binding', _fake_toolchain)


def _batch_root(parent: Path) -> Path:
    root = parent / 'batch-root'
    root.mkdir(mode=0o700, exist_ok=True)
    root.chmod(0o700)
    return root


def _prepare(parent: Path) -> tuple[Path, dict[str, Any]]:
    parent.mkdir(mode=0o700, parents=True, exist_ok=True)
    parent.chmod(0o700)
    material = _materials()
    root = parent / 'child'
    static = runner.prepare_root_from_material(
        root, batch_root=_batch_root(parent),
        parent_manifest=material['parent'], width6_campaign=material['width6'],
        width10_campaign=material['width10'], overlay_manifest=material['overlay'],
        hard_evidence=material['hard'], switch_evidence=material['switch'],
        expected_overlay_sha256=material['overlay']['manifest_sha256'],
        expected_hard_evidence_sha256=material['hard']['evidence_sha256'],
        expected_switch_evidence_sha256=material['switch']['record_sha256'],
        expected_batch_manifest_sha256=BATCH_PIN, descendant_index=0,
        candidate_variables=[1], timeout_seconds=60.0,
        elapsed_seconds_by_lane=[60.1, 60.2, 60.3, 60.4],
        resource_caps=CAPS, instance=TEST_INSTANCE, strict_base=False,
        switch_verifier=_switch_verifier, science_modules=SCIENCE,
    )
    return root, static


class _FakeTransport:
    def __init__(self, monkeypatch: pytest.MonkeyPatch) -> None:
        self.state = 'INITIALIZED'
        self.config: dict[str, Any] | None = None
        self.active: dict[str, Any] | None = None
        self.checkpoint: dict[str, Any] | None = None
        self.cpu = min(os.sched_getaffinity(0))
        monkeypatch.setattr(runner, '_single_cpu', lambda: self.cpu)
        monkeypatch.setattr(runner, '_preflight_cpu', lambda cpu: None)
        monkeypatch.setattr(runner, '_preflight_solver_limits', lambda cap: None)
        monkeypatch.setattr(runner, '_admit_live_peer', self._admit)
        monkeypatch.setattr(runner, '_inherited_solver_limits', self._limits)
        monkeypatch.setattr(controller, 'initialize', self.initialize)
        monkeypatch.setattr(controller, 'start', self.start)
        monkeypatch.setattr(controller, 'checkpoint_stop', self.checkpoint_stop)
        monkeypatch.setattr(controller, 'resume', self.resume)
        monkeypatch.setattr(controller, 'inspect', self.inspect)

    @contextlib.contextmanager
    def _limits(self, cap: int) -> Iterator[None]:
        yield

    def _admit(self, result: Mapping[str, Any], *, cpu: int, cap: int) -> dict[str, Any]:
        return {
            'pid': result['pid'], 'proof_fsize_soft_bytes': cap,
            'proof_fsize_hard_bytes': -1, 'core_soft_bytes': 0,
            'core_hard_bytes': -1, 'cpu_soft_seconds': -1,
            'cpu_hard_seconds': -1, 'verified': True,
        }

    def initialize(self, root: Path, **kwargs: Any) -> dict[str, Any]:
        root.mkdir(mode=0o700)
        for name in ('proof.drat', 'solver.stdout', 'solver.stderr'):
            (root / name).write_bytes(b'')
            (root / name).chmod(0o600)
        self.config = controller.seal_manifest('init.commit', {'root': str(root.resolve())})
        return self.config

    def start(self, root: Path) -> dict[str, Any]:
        self.active = controller.seal_manifest(
            'start.commit', {'pid': 990001, 'proc_start_ticks': 11, 'generation': 0},
        )
        self.state = 'RUNNING'
        return self.active

    def checkpoint_stop(self, root: Path) -> dict[str, Any]:
        self.checkpoint = controller.seal_manifest(
            'checkpoint.commit', {'generation': self.active['generation']},
        )
        self.state = 'CHECKPOINTED'
        return self.checkpoint

    def resume(self, root: Path) -> dict[str, Any]:
        generation = self.active['generation'] + 1
        self.active = controller.seal_manifest(
            'resume.commit', {'pid': 990001 + generation, 'proc_start_ticks': 11 + generation, 'generation': generation},
        )
        self.checkpoint = None
        self.state = 'RUNNING'
        return self.active

    def inspect(self, root: Path, *, verify_hashes: bool) -> dict[str, Any]:
        assert verify_hashes and self.config is not None
        generations: list[dict[str, Any]] = []
        if self.active is not None:
            generations = [{
                'generation': self.active['generation'], 'poison_claim': None,
                'active_manifest_sha256': self.active['self_sha256'],
                'pid': self.active['pid'],
                'proc_start_ticks': self.active['proc_start_ticks'],
                'pid_identity_alive': self.state == 'RUNNING',
                'checkpoint_manifest_sha256': None if self.checkpoint is None else self.checkpoint['self_sha256'],
            }]
        return {
            'authority': controller.AUTHORITY,
            'config_manifest_sha256': self.config['self_sha256'],
            'dmtcp_command_sha256': 'e' * 64, 'generations': generations,
            'hash_verification_requested': True, 'root': str(root.resolve()),
            'state': self.state,
        }


def _action_kwargs() -> dict[str, Any]:
    return {
        'instance': TEST_INSTANCE, 'switch_verifier': _switch_verifier,
        'science_modules': SCIENCE,
    }


def _install_real_tiny_proof(root: Path) -> None:
    runtime = root / runner.RUNTIME_ROOT
    result = subprocess.run(
        [str(runner.SOLVER), '-q', str(root / runner.STATIC_DESCENDANT_CNF), str(runtime / 'proof.drat')],
        stdin=subprocess.DEVNULL, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
        timeout=30, check=False, env={'LANG': 'C', 'LC_ALL': 'C', 'PATH': '/usr/bin:/bin'},
    )
    assert result.returncode == 20 and result.stderr == b''
    (runtime / 'solver.stdout').write_bytes(result.stdout)
    for name in ('proof.drat', 'solver.stdout', 'solver.stderr'):
        (runtime / name).chmod(0o600)


def test_prepare_exact_candidate_and_static_tamper(tmp_path: Path) -> None:
    root, static = _prepare(tmp_path)
    assert static['strict_base'] is False
    assert static['launch_attestation']['atomic_switch_v4_lease_required'] is True
    assert static['python_startup']['strict_base'] is False
    assert (root / runner.STATIC_DESCENDANT_CNF).read_bytes() == _render(PARENT_DIMACS, [1])
    with (root / runner.STATIC_DESCENDANT_CNF).open('ab') as stream:
        stream.write(b'c tamper\n')
    with pytest.raises(runner.AdaptiveChildResumeError):
        runner._load_static(root, **_action_kwargs())


def test_session_action_exact_fields_checkpoint_resume_and_status_readonly(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    root, _ = _prepare(tmp_path)
    transport = _FakeTransport(monkeypatch)
    session = runner.start_root(root, **_action_kwargs())
    stopped = runner.checkpoint_stop_root(root, **_action_kwargs())
    resumed = runner.resume_root(root, **_action_kwargs())
    before = sorted((root / runner.ACTIONS_DIR).iterdir())
    status = runner.status_root(root, **_action_kwargs())
    after = sorted((root / runner.ACTIONS_DIR).iterdir())
    assert status['read_only'] is True and before == after
    assert stopped['transition'] == 'CHECKPOINTED_STOPPED'
    assert resumed['transition'] == 'RESUMED_RUNNING'
    assert session['python_startup_sha256']
    pairs = runner._action_pairs(root)
    assert [claim['action'] for claim, _ in pairs] == ['start', 'checkpoint-stop', 'resume']
    altered = dict(session)
    altered.pop('record_sha256')
    altered['forged_extra'] = True
    runner._publish_json(root / Path('state/11-forged-session.json'), runner.seal(altered))
    with pytest.raises(runner.AdaptiveChildResumeError, match='session/static'):
        runner._validate_session_value(
            root, runner._load_static(root, **_action_kwargs()), runner.seal(altered),
        )
    bad_limits = dict(session['started_peer_rlimits'])
    bad_limits['verified'] = False
    with pytest.raises(runner.AdaptiveChildResumeError, match='RLIMIT'):
        runner._validate_peer_rlimits(
            bad_limits,
            expected_pid=session['controller_start_pid'],
            cap=session['proof_cap_bytes'],
        )
    for field in ("started_peer_rlimits", "rlimit_policy"):
        altered = dict(session)
        altered.pop("record_sha256")
        if field == "started_peer_rlimits":
            altered.pop(field)
        else:
            altered[field] = dict(altered[field])
            altered[field]["cpu_soft_seconds"] = 10
        with pytest.raises(
            runner.AdaptiveChildResumeError, match="session/static",
        ):
            runner._validate_session_value(
                root, runner._load_static(root, **_action_kwargs()),
                runner.seal(altered),
            )
    assert transport.state == 'RUNNING'


def test_inherited_solver_limits_raise_cpu_soft_and_restore_on_exception() -> None:
    old_cpu = resource.getrlimit(resource.RLIMIT_CPU)
    old_fsize = resource.getrlimit(resource.RLIMIT_FSIZE)
    old_core = resource.getrlimit(resource.RLIMIT_CORE)
    if old_cpu[1] != resource.RLIM_INFINITY:
        pytest.skip("test requires unlimited hard CPU rlimit")
    finite_soft = max(3600, int(time.process_time()) + 60)
    resource.setrlimit(
        resource.RLIMIT_CPU, (finite_soft, resource.RLIM_INFINITY),
    )
    try:
        with pytest.raises(RuntimeError, match="body fault"):
            with runner._inherited_solver_limits(1 << 20):
                assert resource.getrlimit(resource.RLIMIT_CPU) == (
                    resource.RLIM_INFINITY, resource.RLIM_INFINITY,
                )
                assert resource.getrlimit(resource.RLIMIT_FSIZE)[0] == 1 << 20
                assert resource.getrlimit(resource.RLIMIT_CORE)[0] == 0
                raise RuntimeError("body fault")
        assert resource.getrlimit(resource.RLIMIT_CPU) == (
            finite_soft, resource.RLIM_INFINITY,
        )
        assert resource.getrlimit(resource.RLIMIT_FSIZE) == old_fsize
        assert resource.getrlimit(resource.RLIMIT_CORE) == old_core
    finally:
        resource.setrlimit(resource.RLIMIT_CPU, old_cpu)


def test_finite_hard_cpu_rejected_before_action_claim(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    root = tmp_path / "finite-hard"
    root.mkdir(mode=0o700)
    calls: list[str] = []
    real_getrlimit = resource.getrlimit

    def fake_getrlimit(which: int) -> tuple[int, int]:
        if which == resource.RLIMIT_CPU:
            return (10, 20)
        return real_getrlimit(which)

    monkeypatch.setattr(resource, "getrlimit", fake_getrlimit)
    monkeypatch.setattr(
        runner, "_begin_action",
        lambda *args, **kwargs: calls.append("claim"),
    )
    with pytest.raises(
        runner.AdaptiveChildResumeError, match="hard RLIMIT_CPU",
    ):
        runner._start_locked(
            root,
            {"record": {"resource_policy": {"proof_max_bytes": 1 << 20}}},
            cpu=min(os.sched_getaffinity(0)), pin_parent_cpu=False,
        )
    assert calls == []


def test_live_peer_finite_cpu_rlimit_rejected(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    cap = 1 << 20

    def fake_prlimit(pid: int, which: int) -> tuple[int, int]:
        del pid
        return {
            resource.RLIMIT_FSIZE: (cap, resource.RLIM_INFINITY),
            resource.RLIMIT_CORE: (0, resource.RLIM_INFINITY),
            resource.RLIMIT_CPU: (10, resource.RLIM_INFINITY),
        }[which]

    monkeypatch.setattr(resource, "prlimit", fake_prlimit)
    with pytest.raises(runner.AdaptiveChildResumeError, match="RLIMIT"):
        runner._verify_live_peer_rlimits(12345, cap)


def test_strict_direct_resume_rejected_before_transport(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    root = tmp_path / 'strict-resume'
    root.mkdir(mode=0o700)
    root.chmod(0o700)
    runner._initialize_outer_lock(root)
    loaded = {'record': {'strict_base': True}}
    session = {
        'record_sha256': '2' * 64,
        'expected_single_cpu': min(os.sched_getaffinity(0)),
    }
    monkeypatch.setattr(runner, '_load_static', lambda *args, **kwargs: loaded)
    monkeypatch.setattr(runner, '_load_session', lambda *args, **kwargs: session)
    monkeypatch.setattr(
        runner, '_verify_complete_handoff_links',
        lambda *args, **kwargs: {'valid': True},
    )
    monkeypatch.setattr(
        runner, '_inspect_controller',
        lambda *args, **kwargs: (
            _ for _ in ()
        ).throw(AssertionError('transport touched')),
    )
    with pytest.raises(
        runner.AdaptiveChildResumeError,
        match='eight-root cohort scheduler',
    ):
        runner.resume_root(root)
    assert not list((root / runner.ACTIONS_DIR).glob('*')) if (
        root / runner.ACTIONS_DIR
    ).exists() else True


def test_post_spawn_admission_failure_kills_pid_and_leaves_no_writer(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    root = tmp_path / 'postspawn'
    root.mkdir(mode=0o700)
    root.chmod(0o700)
    runner._initialize_outer_lock(root)
    for name in ('static', 'state', 'artifacts', 'runtime'):
        runner._mkdir(root, name)
    runner._mkdir(root / 'state', 'actions')
    runtime = root / runner.RUNTIME_ROOT
    state = {'value': 'INITIALIZED'}
    active: dict[str, Any] = {}
    config: dict[str, Any] = {}
    process: subprocess.Popen[bytes] | None = None
    static = runner.seal({
        'kind': runner.STATIC_KIND, 'gate': runner.GATE, 'root': str(root),
        'resource_policy': {'proof_max_bytes': 1 << 20},
        'toolchain_binding': {
            'tools': {'cadical_solver': {'path': '/bin/true'}},
            'runtime_libraries': [], 'dmtcp': {'prefix': '/tmp'},
        },
    })
    runner._publish_json(root / runner.STATIC_COMMIT, static)

    def initialize(path: Path, **kwargs: Any) -> dict[str, Any]:
        path.mkdir(mode=0o700)
        (path / 'proof.drat').write_bytes(b'partial-proof\n')
        (path / 'proof.drat').chmod(0o600)
        config.update(controller.seal_manifest('init.commit', {'root': str(path.resolve())}))
        return dict(config)

    def start(path: Path) -> dict[str, Any]:
        nonlocal process
        process = subprocess.Popen(
            ['/usr/bin/tail', '-f', '/dev/null'], stdin=subprocess.DEVNULL,
            stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL,
            start_new_session=True,
        )
        ticks = controller._proc_start_ticks(process.pid)
        active.update(controller.seal_manifest(
            'start.commit', {'pid': process.pid, 'proc_start_ticks': ticks, 'generation': 0},
        ))
        state['value'] = 'RUNNING'
        return dict(active)

    def stop(path: Path) -> dict[str, Any]:
        assert process is not None
        os.killpg(process.pid, signal.SIGTERM)
        process.wait(timeout=10)
        state['value'] = 'CHECKPOINTED'
        return controller.seal_manifest('checkpoint.commit', {'generation': 0})

    def inspect(path: Path, *, verify_hashes: bool) -> dict[str, Any]:
        return {
            'authority': controller.AUTHORITY,
            'config_manifest_sha256': config['self_sha256'],
            'dmtcp_command_sha256': 'e' * 64,
            'generations': [{
                'generation': 0, 'poison_claim': None,
                'active_manifest_sha256': active['self_sha256'],
                'pid': active['pid'], 'proc_start_ticks': active['proc_start_ticks'],
                'pid_identity_alive': state['value'] == 'RUNNING',
                'checkpoint_manifest_sha256': 'f' * 64 if state['value'] == 'CHECKPOINTED' else None,
            }],
            'hash_verification_requested': True, 'root': str(path.resolve()),
            'state': state['value'],
        }

    monkeypatch.setattr(controller, 'initialize', initialize)
    monkeypatch.setattr(controller, 'start', start)
    monkeypatch.setattr(controller, 'checkpoint_stop', stop)
    monkeypatch.setattr(controller, 'inspect', inspect)
    monkeypatch.setattr(runner, '_preflight_solver_limits', lambda cap: None)
    monkeypatch.setattr(runner, '_preflight_cpu', lambda cpu: None)
    monkeypatch.setattr(runner, '_inherited_solver_limits', lambda cap: contextlib.nullcontext())
    monkeypatch.setattr(runner, '_admit_live_peer', lambda *args, **kwargs: (_ for _ in ()).throw(RuntimeError('admit fault')))
    loaded = {'record': static}
    with pytest.raises(runner._PostSpawnFailure, match='admit fault') as caught:
        runner._start_locked(root, loaded, cpu=min(os.sched_getaffinity(0)), pin_parent_cpu=False)
    assert process is not None and process.poll() is not None
    assert caught.value.quiescence['pid_identity_alive'] is False
    assert caught.value.quiescence['writable_holders'] == []
    assert runner._writable_holders(runtime / 'proof.drat') == []


class _Permit:
    def __init__(self, key: tuple[int, int], target: Mapping[str, Any]) -> None:
        self.key = key
        self.target = dict(target)


class _FakeOuterLock:
    def __init__(self, root: Path, fd: int) -> None:
        self.root = root
        self.fd = fd
        self.transferred = False

    def fileno(self) -> int:
        assert not self.transferred
        return self.fd

    def complete_transfer(self) -> None:
        self.transferred = True


class _FakeLease:
    def __init__(self, fail_note: tuple[int, int] | None = None) -> None:
        self.fail_note = fail_note
        self.permits: dict[tuple[int, int], _Permit] = {}
        self.started: dict[tuple[int, int], dict[str, Any]] = {}
        self.note_order: list[tuple[tuple[int, int], bool]] = []
        self.rollback: dict[str, Any] | None = None
        self.commits = 0
        self.adopted: list[int] | None = None
        self.transition = object()

    def verify_target(self, **kwargs: Any) -> _Permit:
        key = (kwargs['global_leaf_index'], kwargs['descendant_index'])
        permit = _Permit(key, kwargs)
        self.permits[key] = permit
        return permit

    def prepare_target(
        self, *, permit: _Permit,
        new_root_identity: Mapping[str, Any],
    ) -> dict[str, Any]:
        return runner.seal({
            'target_key': list(permit.key),
            'root': dict(new_root_identity),
        })

    def adopt_prepared_outer_locks(
        self, *, outer_lock_fds: list[int],
    ) -> None:
        assert len(outer_lock_fds) == runner.COVER_ROOT_COUNT
        self.adopted = list(outer_lock_fds)

    def note_started_worker(
        self, *, permit: _Permit, cohort_transition_permit: Any | None,
        **kwargs: Any,
    ) -> object:
        # Register before the simulated durable publication fault.
        self.started[permit.key] = dict(kwargs)
        self.note_order.append(
            (permit.key, cohort_transition_permit is self.transition)
        )
        if permit.key == self.fail_note:
            raise RuntimeError('note journal publication fault')
        return SimpleNamespace(key=permit.key)

    def started_target_keys(self) -> list[tuple[int, int]]:
        return list(self.started)

    def post_start_fence(
        self, *, permit: _Permit, started_worker: object, **kwargs: Any,
    ) -> object:
        return SimpleNamespace(key=permit.key, values=dict(kwargs))

    def note_cohort_checkpointed(
        self, *, quiescence_records: list[dict[str, Any]],
    ) -> object:
        assert [
            (item['lane_index'], item['descendant_index'])
            for item in quiescence_records
        ] == list(runner.TARGET_KEYS[:runner.COHORT_SIZE])
        return self.transition

    def commit_handoff(
        self, *, fences: list[Any], batch_commit_path: Path,
    ) -> dict[str, Any]:
        del batch_commit_path
        self.commits += 1
        assert [fence.key for fence in fences] == list(runner.TARGET_KEYS)
        bindings = [
            {
                'lane_index': key[0], 'descendant_index': key[1],
                'new_root_identity': dict(self.started[key]['new_root_identity']),
            }
            for key in runner.TARGET_KEYS
        ]
        return runner.seal({
            'launch_authorized': False,
            'prepared_retirement_sha256': '8' * 64,
            'root_bindings': bindings,
        })

    def rollback_after_new_quiescent(self, **kwargs: Any) -> dict[str, Any]:
        self.rollback = kwargs
        return {
            'launch_authorized': False,
            'new_workers_quiescent': True,
        }


def _atomic_entries(
    tmp_path: Path,
) -> tuple[list[dict[str, Any]], list[_FakeOuterLock]]:
    entries: list[dict[str, Any]] = []
    locks: list[_FakeOuterLock] = []
    for position, (lane, descendant) in enumerate(runner.TARGET_KEYS):
        root = tmp_path / f'lane-{lane}-desc-{descendant}'
        root.mkdir(mode=0o700)
        root.chmod(0o700)
        entries.append({
            'root': root, 'cpu': lane, 'lane_index': lane,
            'descendant_index': descendant,
            'target_key': (lane, descendant),
            'loaded': {
                'overlay': {},
                'record': {
                    'external_pins': {
                        'expected_overlay_sha256': f'{lane + 10:064x}',
                        'expected_hard_evidence_sha256': f'{lane + 20:064x}',
                    },
                    'selection': {
                        'global_leaf_index': lane,
                        'candidate_variables': [1],
                        'descendant_index': descendant,
                        'descendant_sha256': f'{position + 30:064x}',
                    },
                },
            },
        })
        locks.append(_FakeOuterLock(root, 100 + position))
    return entries, locks


def _fake_quiescence(
    root: Path, lane: int, descendant: int, pid: int, ticks: int,
) -> dict[str, Any]:
    return runner.seal({
        'schema_version': 5,
        'kind': 'paper400-adaptive-new-root-quiescence-observation-v5',
        'lane_index': lane, 'descendant_index': descendant,
        'new_root_identity': runner._directory_identity(
            root, require_mode_0700=True,
        ),
        'new_pid': pid, 'new_proc_start_ticks': ticks,
        'state': 'CHECKPOINTED', 'pid_identity_alive': False,
        'checkpoint_commit_sha256': 'a' * 64,
        'proof_sha256': '9' * 64, 'proof_bytes': 0,
        'writable_holders': [],
    })


def _install_atomic_transport_fakes(
    monkeypatch: pytest.MonkeyPatch, lease: _FakeLease,
    cleanup: list[tuple[int, int]],
) -> None:
    def fake_start(
        root: Path, loaded: Mapping[str, Any], *, cpu: int,
        pin_parent_cpu: bool, lane_index: int, descendant_index: int,
        started_hook: Any,
    ) -> dict[str, Any]:
        del loaded, cpu, pin_parent_cpu
        key = (lane_index, descendant_index)
        active = controller.seal_manifest(
            'start.commit', {
                'pid': 800000 + 10 * descendant_index + lane_index,
                'proc_start_ticks': 900000 + 10 * descendant_index + lane_index,
            },
        )
        try:
            worker = started_hook(active)
        except BaseException as exc:
            quiescence = _fake_quiescence(
                root, lane_index, descendant_index,
                active['pid'], active['proc_start_ticks'],
            )
            failure = runner._PostSpawnFailure(
                f'note failed: {exc}', quiescence,
            )
            failure.__cause__ = exc
            raise failure
        return {
            'session': runner.seal({
                'lane': lane_index, 'descendant': descendant_index,
            }),
            'action_commit': runner.seal({
                'lane': lane_index, 'descendant': descendant_index,
            }),
            'controller_start': active, 'started_worker': worker,
        }

    def fake_stop(
        root: Path, started: Mapping[str, Any], *, lane_index: int,
        descendant_index: int,
    ) -> dict[str, Any]:
        cleanup.append((lane_index, descendant_index))
        active = started['controller_start']
        return _fake_quiescence(
            root, lane_index, descendant_index,
            active['pid'], active['proc_start_ticks'],
        )

    def fake_checkpoint(
        root: Path, *, batch_token: Any, **kwargs: Any,
    ) -> dict[str, Any]:
        del root, batch_token, kwargs
        return runner.seal({'checkpoint': True})

    def fake_committed(
        root: Path, lane_index: int, descendant_index: int,
        loaded: Mapping[str, Any],
    ) -> dict[str, Any]:
        del loaded
        active = lease.started[(lane_index, descendant_index)]
        return _fake_quiescence(
            root, lane_index, descendant_index,
            active['new_pid'], active['new_proc_start_ticks'],
        )

    monkeypatch.setattr(runner, '_start_locked', fake_start)
    monkeypatch.setattr(runner, '_stop_failed_new_root', fake_stop)
    monkeypatch.setattr(runner, '_checkpoint_stop_locked', fake_checkpoint)
    monkeypatch.setattr(runner, '_committed_quiescence_record', fake_committed)
    monkeypatch.setattr(
        runner, '_temporary_cpu', lambda cpu: contextlib.nullcontext(),
    )


def test_atomic_note_journal_fault_is_quiescent_not_not_started(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    entries, locks = _atomic_entries(tmp_path)
    lease = _FakeLease(fail_note=(1, 0))
    cleanup: list[tuple[int, int]] = []
    _install_atomic_transport_fakes(monkeypatch, lease, cleanup)
    with pytest.raises(runner._PostSpawnFailure, match='note failed'):
        runner._atomic_handoff_start(
            lease, entries, batch_commit_path=tmp_path / 'commit.json',
            outer_locks=locks,
        )
    assert cleanup == [(0, 0)]
    assert all(lock.transferred for lock in locks)
    assert lease.commits == 0 and lease.rollback is not None
    assert [
        (item['lane_index'], item['descendant_index'])
        for item in lease.rollback['quiescence_records']
    ] == [(0, 0), (1, 0)]
    assert lease.rollback['not_started_target_keys'] == list(
        runner.TARGET_KEYS[2:]
    )


def test_atomic_complete_cover_starts_cohorts_in_order_and_commits(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    entries, locks = _atomic_entries(tmp_path)
    lease = _FakeLease()
    cleanup: list[tuple[int, int]] = []
    _install_atomic_transport_fakes(monkeypatch, lease, cleanup)
    commit, started = runner._atomic_handoff_start(
        lease, entries, batch_commit_path=tmp_path / 'commit.json',
        outer_locks=locks,
    )
    assert commit['prepared_retirement_sha256'] == '8' * 64
    assert len(started) == runner.COVER_ROOT_COUNT
    assert lease.note_order == [
        *((key, False) for key in runner.TARGET_KEYS[:runner.COHORT_SIZE]),
        *((key, True) for key in runner.TARGET_KEYS[runner.COHORT_SIZE:]),
    ]
    assert lease.commits == 1 and cleanup == []


def test_frozen_switch_v2_v4_exact_loader_and_record_cannot_select_source() -> None:
    module = runner._switch_v4_module(runner._SWITCH_V4_SOURCE_SHA256)
    assert (
        module._V4_SOURCE_RECORD["sha256"]
        == runner._SWITCH_V4_SOURCE_SHA256
    )
    assert (
        module._BASE_SOURCE_RECORD["sha256"]
        == runner._SWITCH_V2_SOURCE_SHA256
    )
    _, overlay_source, overlay_executed = module._load_overlay_exact()
    serialized_overlay_source = dict(overlay_source)
    serialized_overlay_source["execution"] = "compile-exact-source-bytes-v3"
    binding = module.base._source_binding(
        {"legacy_project": str(runner.PROJECT), "legacy_sources": []},
        [], serialized_overlay_source, overlay_executed,
    )
    record = {"source_binding": binding}
    assert (
        runner._switch_record_overlay_source(record)
        == runner.canonical_bytes(serialized_overlay_source)
    )
    v4_tag_record = {
        "source_binding": module.base._source_binding(
            {"legacy_project": str(runner.PROJECT), "legacy_sources": []},
            [], overlay_source, overlay_executed,
        ),
    }
    with pytest.raises(
        runner.AdaptiveChildResumeError, match="overlay source binding",
    ):
        runner._switch_record_overlay_source(v4_tag_record)
    modules = runner._science_modules(record)
    assert modules[0].__file__ == str(
        runner.PROJECT
        / "investigations/paper400_dic5_adaptive_leaf_overlay_v2.py"
    )

    forged_v2 = json.loads(json.dumps(record))
    forged_v2["source_binding"]["current_sources"][0]["sha256"] = (
        "0" * 64
    )
    forged_v2["source_binding"].pop("source_binding_sha256")
    forged_v2["source_binding"] = module.base.seal(
        forged_v2["source_binding"], "source_binding_sha256",
    )
    with pytest.raises(
        runner.AdaptiveChildResumeError, match="frozen v2",
    ):
        runner._switch_record_overlay_source(forged_v2)

    forged_overlay = json.loads(json.dumps(record))
    forged_overlay["source_binding"]["current_sources"][1]["sha256"] = (
        "0" * 64
    )
    forged_overlay["source_binding"].pop("source_binding_sha256")
    forged_overlay["source_binding"] = module.base.seal(
        forged_overlay["source_binding"], "source_binding_sha256",
    )
    with pytest.raises(
        runner.AdaptiveChildResumeError, match="overlay source binding",
    ):
        runner._switch_record_overlay_source(forged_overlay)

    with pytest.raises(
        runner.AdaptiveChildResumeError, match="real v2 schema",
    ):
        runner._switch_record_overlay_source({
            "source_binding": module._v4_source_binding(),
        })
    with pytest.raises(
        runner.AdaptiveChildResumeError, match="frozen pin",
    ):
        runner._switch_v4_module("0" * 64)


def test_runner_quiescence_schema_is_accepted_by_frozen_switch_v4(
    tmp_path: Path,
) -> None:
    root = tmp_path / "quiescence-root"
    root.mkdir(mode=0o700)
    root.chmod(0o700)
    switch = runner._switch_v4_module(runner._SWITCH_V4_SOURCE_SHA256)

    def record(state: str, checkpoint: str | None) -> dict[str, Any]:
        return runner.seal({
            "schema_version": 5,
            "kind": "paper400-adaptive-new-root-quiescence-observation-v5",
            "lane_index": 0,
            "descendant_index": 0,
            "new_root_identity": runner._directory_identity(
                root, require_mode_0700=True,
            ),
            "new_pid": 12345,
            "new_proc_start_ticks": 67890,
            "state": state,
            "pid_identity_alive": False,
            "checkpoint_commit_sha256": checkpoint,
            "proof_sha256": hashlib.sha256(b"").hexdigest(),
            "proof_bytes": 0,
            "writable_holders": [],
        })

    checked = record("CHECKPOINTED", "a" * 64)
    assert switch._validate_quiescence_record(checked) == checked
    inactive = record("INACTIVE_UNCHECKPOINTED", None)
    assert switch._validate_quiescence_record(inactive) == inactive
    missing = dict(checked)
    missing.pop("record_sha256")
    missing.pop("checkpoint_commit_sha256")
    with pytest.raises(switch.AdaptiveSwitchEvidenceV4Error):
        switch._validate_quiescence_record(runner.seal(missing))
    bad = dict(inactive)
    bad.pop("record_sha256")
    bad["checkpoint_commit_sha256"] = "b" * 64
    with pytest.raises(switch.AdaptiveSwitchEvidenceV4Error):
        switch._validate_quiescence_record(runner.seal(bad))


def test_real_switch_lane_layout_maps_exact_eight_targets() -> None:
    lanes = [
        {
            'lane_index': lane, 'global_leaf_index': 100 + lane,
            'hard_evidence_sha256': f'{lane + 1:064x}',
        }
        for lane in range(runner.LANE_COUNT)
    ]
    switch = {'lanes': lanes}
    loaded = []
    for lane, descendant in runner.TARGET_KEYS:
        hard = lanes[lane]['hard_evidence_sha256']
        record = {
            'batch_root_identity': {'path': '/tmp/batch'},
            'switch_evidence_sha256': 'a' * 64,
            'switch_policy': {
                'timeout_seconds': 60.0,
                'elapsed_seconds_by_lane': [60.1, 60.2, 60.3, 60.4],
            },
            'external_pins': {
                'expected_switch_evidence_sha256': 'a' * 64,
                'expected_batch_manifest_sha256': 'b' * 64,
                'expected_hard_evidence_sha256': hard,
            },
            'selection': {
                'global_leaf_index': 100 + lane,
                'descendant_index': descendant,
                'candidate_variables': [1],
            },
        }
        loaded.append({'record': record, 'switch_evidence': switch})
    common = runner._batch_common(loaded)
    assert common['expected_hard_evidence_sha256s'] == [
        lane['hard_evidence_sha256'] for lane in lanes
    ]
    assert 'hard_evidence_sha256s' not in switch
    bad = json.loads(json.dumps(loaded))
    for item in bad:
        item['switch_evidence']['lanes'][0]['lane_index'] = 3
    with pytest.raises(runner.AdaptiveChildResumeError, match='lane layout'):
        runner._batch_common(bad)


def _v4_cover_fixture(
    tmp_path: Path, *, strict_base: bool,
) -> tuple[list[Path], list[dict[str, Any]], Path, dict[str, Any]]:
    tmp_path.chmod(0o700)
    batch_root = tmp_path / 'old-batch'
    batch_root.mkdir(mode=0o700)
    batch_root.chmod(0o700)
    lanes = [
        {
            'lane_index': lane,
            'global_leaf_index': 100 + lane,
            'hard_evidence_sha256': f'{lane + 1:064x}',
        }
        for lane in range(runner.LANE_COUNT)
    ]
    switch = {'record_sha256': 'a' * 64, 'lanes': lanes}
    roots: list[Path] = []
    loaded: list[dict[str, Any]] = []
    for position, (lane, descendant) in enumerate(runner.TARGET_KEYS):
        root = tmp_path / f'v4-root-{lane}-{descendant}'
        root.mkdir(mode=0o700)
        root.chmod(0o700)
        (root / 'state').mkdir(mode=0o700)
        runner._initialize_outer_lock(root)
        roots.append(root)
        loaded.append({
            'overlay': {},
            'switch_evidence': switch,
            'record': {
                'record_sha256': f'{position + 100:064x}',
                'strict_base': strict_base,
                'batch_root_identity': {'path': str(batch_root)},
                'switch_evidence_sha256': 'a' * 64,
                'switch_policy': {
                    'timeout_seconds': 60.0,
                    'elapsed_seconds_by_lane': [60.1, 60.2, 60.3, 60.4],
                },
                'external_pins': {
                    'expected_overlay_sha256': f'{lane + 20:064x}',
                    'expected_hard_evidence_sha256':
                        lanes[lane]['hard_evidence_sha256'],
                    'expected_switch_evidence_sha256': 'a' * 64,
                    'expected_batch_manifest_sha256': 'b' * 64,
                },
                'selection': {
                    'global_leaf_index': 100 + lane,
                    'candidate_variables': [390],
                    'descendant_index': descendant,
                    'descendant_sha256': f'{position + 200:064x}',
                },
                'execution_module_binding': {
                    'switch_v4_source_sha256': 'c' * 64,
                },
                'resource_policy': {'proof_max_bytes': 64 << 20},
            },
        })
    return roots, loaded, batch_root, switch


def test_inspect_incident_batch_calls_readonly_builder_once_in_canonical_order(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    roots, loaded, batch_root, _ = _v4_cover_fixture(
        tmp_path, strict_base=True,
    )
    by_root = dict(zip(roots, loaded, strict=True))
    calls: list[dict[str, Any]] = []
    attempt = 'd' * 64

    def build_incident(
        observed_batch_root: Path, **kwargs: Any,
    ) -> dict[str, Any]:
        calls.append({
            'batch_root': observed_batch_root,
            **kwargs,
        })
        return runner.seal({
            'attempt_id': attempt,
            'batch_root': str(batch_root),
            'batch_manifest_sha256': 'b' * 64,
            'switch_evidence_sha256': 'a' * 64,
            'target_roots': [
                {'path': str(root)} for root in kwargs['target_roots']
            ],
            'authenticated': False,
            'launch_authorized': False,
            'scientific_claim': False,
        })

    monkeypatch.setattr(
        runner, '_load_static',
        lambda root, **kwargs: by_root[Path(root)],
    )
    monkeypatch.setattr(
        runner, '_switch_v4_module',
        lambda source_sha: SimpleNamespace(
            ATTEMPT_ID=attempt,
            build_incident_precondition=build_incident,
        ),
    )
    observed = runner.inspect_incident_batch(roots)
    assert observed['attempt_id'] == attempt
    assert len(calls) == 1
    assert calls[0]['batch_root'] == batch_root
    assert calls[0]['target_roots'] == roots
    assert calls[0]['strict_base'] is True
    assert calls[0]['timeout_seconds'] == 60.0
    assert calls[0]['elapsed_seconds_by_lane'] == [
        60.1, 60.2, 60.3, 60.4,
    ]
    assert not (batch_root / 'adaptive-handoff-v4-unexpected').exists()


def test_new_output_path_allows_one_absent_attempt_parent(
    tmp_path: Path,
) -> None:
    tmp_path.chmod(0o700)
    parent = tmp_path / f"adaptive-handoff-v4-attempt-{'d' * 64}"
    target = parent / '90-handoff.json'
    runner._validate_new_output_path(
        target, label='batch handoff commit',
        parent_may_be_absent=True,
    )
    assert not parent.exists()


def test_new_output_path_default_rejects_absent_parent(
    tmp_path: Path,
) -> None:
    tmp_path.chmod(0o700)
    target = tmp_path / 'attempt' / '90-handoff.json'
    with pytest.raises(runner.AdaptiveChildResumeError):
        runner._validate_new_output_path(target, label='ordinary output')


def test_new_output_path_rejects_symlink_parent_when_absence_allowed(
    tmp_path: Path,
) -> None:
    tmp_path.chmod(0o700)
    parent = tmp_path / 'attempt'
    parent.symlink_to(tmp_path / 'missing-target', target_is_directory=True)
    with pytest.raises(runner.AdaptiveChildResumeError, match='symlink'):
        runner._validate_new_output_path(
            parent / '90-handoff.json', label='batch handoff commit',
            parent_may_be_absent=True,
        )


def test_new_output_path_rejects_multiple_absent_parent_levels(
    tmp_path: Path,
) -> None:
    tmp_path.chmod(0o700)
    target = tmp_path / 'attempt' / 'nested' / '90-handoff.json'
    with pytest.raises(runner.AdaptiveChildResumeError):
        runner._validate_new_output_path(
            target, label='batch handoff commit',
            parent_may_be_absent=True,
        )


def test_start_batch_forwards_external_incident_and_eight_held_outer_fds(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    roots, loaded, batch_root, _ = _v4_cover_fixture(
        tmp_path, strict_base=False,
    )
    by_root = dict(zip(roots, loaded, strict=True))
    cpus = [0, 1, 2, 3] * 2
    incident = 'e' * 64
    attempt = 'd' * 64
    commit_path = tmp_path / 'attempt' / 'handoff.json'
    captured: dict[str, Any] = {}

    @contextlib.contextmanager
    def lease_factory(
        observed_batch_root: Path, **kwargs: Any,
    ) -> Iterator[object]:
        captured['batch_root'] = observed_batch_root
        captured.update(kwargs)
        assert len(kwargs['target_outer_lock_fds']) == runner.COVER_ROOT_COUNT
        assert all(
            os.fstat(descriptor).st_nlink == 1
            for descriptor in kwargs['target_outer_lock_fds']
        )
        commit_path.parent.mkdir(mode=0o700)
        yield object()

    def fake_atomic(
        lease: object, entries: list[dict[str, Any]], **kwargs: Any,
    ) -> tuple[dict[str, Any], list[dict[str, Any]]]:
        del lease, kwargs
        commit_path.write_bytes(b'{}\n')
        return ({
            'record_sha256': 'f' * 64,
            'attempt_id': attempt,
            'incident_precondition_sha256': incident,
            'prepared_retirement_sha256': '8' * 64,
        }, entries)

    monkeypatch.setattr(
        runner, '_cover_roots_cpus',
        lambda observed_roots, observed_cpus: (
            list(observed_roots), list(observed_cpus),
        ),
    )
    monkeypatch.setattr(
        runner, '_load_static',
        lambda root, **kwargs: by_root[Path(root)],
    )
    monkeypatch.setattr(runner, '_preflight_solver_limits', lambda cap: None)
    monkeypatch.setattr(runner, '_atomic_handoff_start', fake_atomic)
    monkeypatch.setattr(
        runner, '_write_handoff_links',
        lambda *args: [
            {'record_sha256': f'{position + 300:064x}'}
            for position in range(runner.COVER_ROOT_COUNT)
        ],
    )
    key_by_root = dict(zip(roots, runner.TARGET_KEYS, strict=True))
    monkeypatch.setattr(
        runner, '_binding_for_root',
        lambda commit, root: {
            'handoff_state': (
                'CHECKPOINTED'
                if key_by_root[Path(root)][1] == 0 else 'RUNNING'
            ),
        },
    )
    monkeypatch.setattr(
        runner, '_switch_v4_module',
        lambda source_sha: (_ for _ in ()).throw(
            AssertionError('start-batch rebuilt public incident')
        ),
    )
    result = runner.start_batch(
        roots, cpus, batch_commit_path=commit_path,
        expected_incident_precondition_sha256=incident,
        instance=TEST_INSTANCE, switch_verifier=_switch_verifier,
        science_modules=SCIENCE, lease_factory=lease_factory,
    )
    assert result['success'] is True
    assert result['attempt_id'] == attempt
    assert result['incident_precondition_sha256'] == incident
    assert captured['batch_root'] == batch_root
    assert captured['target_roots'] == roots
    assert captured['expected_incident_precondition_sha256'] == incident
    assert captured['expected_batch_manifest_sha256'] == 'b' * 64
    assert captured['expected_switch_evidence_sha256'] == 'a' * 64
    assert captured['strict_base'] is False


def test_repair_handoff_links_forwards_v4_attempt_and_incident(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    roots, loaded, _, _ = _v4_cover_fixture(
        tmp_path, strict_base=True,
    )
    by_root = dict(zip(roots, loaded, strict=True))
    attempt = 'd' * 64
    incident = 'e' * 64
    commit = 'f' * 64
    captured: dict[str, Any] = {}

    def verify(path: Path, **kwargs: Any) -> dict[str, Any]:
        captured['path'] = path
        captured.update(kwargs)
        return {'root_bindings': []}

    monkeypatch.setattr(
        runner, '_load_static',
        lambda root, **kwargs: by_root[Path(root)],
    )
    monkeypatch.setattr(
        runner, '_load_session',
        lambda root, loaded_item: {
            'record_sha256': '7' * 64,
            'root_identity': {'path': str(root)},
        },
    )
    monkeypatch.setattr(
        runner, '_switch_v4_module',
        lambda source_sha: SimpleNamespace(
            ATTEMPT_ID=attempt,
            verify_committed_handoff=verify,
        ),
    )
    monkeypatch.setattr(
        runner, '_binding_for_root',
        lambda verified, root: {'new_root_identity': {'path': str(root)}},
    )
    monkeypatch.setattr(
        runner, '_handoff_link_value',
        lambda root, *args: runner.seal({'root': str(root)}),
    )
    commit_path = tmp_path / 'canonical-v4-handoff.json'
    result = runner.repair_handoff_links(
        roots, batch_commit_path=commit_path,
        expected_batch_commit_sha256=commit,
        expected_attempt_id=attempt,
        expected_incident_precondition_sha256=incident,
    )
    assert result['attempt_id'] == attempt
    assert result['incident_precondition_sha256'] == incident
    assert len(result['written_roots']) == runner.COVER_ROOT_COUNT
    assert captured == {
        'path': commit_path,
        'expected_batch_commit_sha256': commit,
        'expected_attempt_id': attempt,
        'expected_incident_precondition_sha256': incident,
        'expected_switch_evidence_sha256': 'a' * 64,
        'expected_batch_manifest_sha256': 'b' * 64,
    }


def test_rollback_handoff_forwards_full_switch_and_neutral_quiescence(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    roots, loaded, _, switch_record = _v4_cover_fixture(
        tmp_path, strict_base=True,
    )
    by_root = dict(zip(roots, loaded, strict=True))
    key_by_root = dict(zip(roots, runner.TARGET_KEYS, strict=True))
    attempt = 'd' * 64
    incident = 'e' * 64
    commit = 'f' * 64
    checkpoint = '9' * 64
    captured: dict[str, Any] = {}

    monkeypatch.setattr(
        runner, 'checkpoint_stop_batch',
        lambda *args, **kwargs: {'record_sha256': checkpoint},
    )
    monkeypatch.setattr(
        runner, '_cover_roots_cpus',
        lambda observed_roots, observed_cpus: (
            list(observed_roots), list(observed_cpus),
        ),
    )
    monkeypatch.setattr(
        runner, '_root_lock',
        lambda *args, **kwargs: contextlib.nullcontext(),
    )
    monkeypatch.setattr(
        runner, '_load_static',
        lambda root, **kwargs: by_root[Path(root)],
    )
    monkeypatch.setattr(
        runner, '_load_session',
        lambda root, loaded_item: {'record_sha256': '7' * 64},
    )
    monkeypatch.setattr(
        runner, '_verify_complete_handoff_links',
        lambda *args, **kwargs: {
            'batch_commit_sha256': commit,
            'attempt_id': attempt,
            'incident_precondition_sha256': incident,
        },
    )
    monkeypatch.setattr(
        runner, '_binding_for_root',
        lambda verified, root: {
            'lane_index': key_by_root[Path(root)][0],
            'descendant_index': key_by_root[Path(root)][1],
        },
    )
    monkeypatch.setattr(
        runner, '_committed_quiescence_record',
        lambda root, lane, descendant, loaded_item: _fake_quiescence(
            root, lane, descendant,
            1000 + 10 * descendant + lane,
            2000 + 10 * descendant + lane,
        ),
    )

    def rollback(path: Path, **kwargs: Any) -> dict[str, Any]:
        captured['path'] = path
        captured.update(kwargs)
        return runner.seal({
            'committed_handoff_sha256': commit,
            'attempt_id': attempt,
            'incident_precondition_sha256': incident,
            'new_workers_quiescent': True,
            'old_checkpoint_replayed': True,
            'authenticated': False,
            'launch_authorized': False,
        })

    monkeypatch.setattr(
        runner, '_switch_v4_module',
        lambda source_sha: SimpleNamespace(
            ATTEMPT_ID=attempt,
            rollback_committed_handoff=rollback,
        ),
    )
    commit_path = tmp_path / 'canonical-v4-handoff.json'
    result = runner.rollback_handoff_batch(
        roots, [0, 1, 2, 3] * 2,
        batch_commit_path=commit_path,
        expected_batch_commit_sha256=commit,
        checkpoint_summary_path=tmp_path / 'checkpoint-summary.json',
    )
    assert result['attempt_id'] == attempt
    assert result['incident_precondition_sha256'] == incident
    assert captured['path'] == commit_path
    assert captured['expected_attempt_id'] == attempt
    assert captured['expected_incident_precondition_sha256'] == incident
    assert captured['expected_switch_record'] is switch_record
    assert len(captured['quiescence_records']) == runner.COVER_ROOT_COUNT
    assert {
        (item['schema_version'], item['kind'])
        for item in captured['quiescence_records']
    } == {
        (
            5,
            'paper400-adaptive-new-root-quiescence-observation-v5',
        ),
    }

def test_handoff_binding_requires_both_durable_journal_hashes(
    tmp_path: Path,
) -> None:
    roots = []
    bindings = []
    for lane, descendant in runner.TARGET_KEYS:
        root = tmp_path / f'binding-{lane}-{descendant}'
        roots.append(root)
        bindings.append({
            'lane_index': lane, 'global_leaf_index': 100 + lane,
            'descendant_index': descendant,
            'descendant_sha256': '1' * 64,
            'new_root_identity': {'path': str(root)},
            'new_session_sha256': '2' * 64,
            'new_start_commit_sha256': '3' * 64,
            'new_pid': 1000 + 10 * descendant + lane,
            'new_proc_start_ticks': 2000 + 10 * descendant + lane,
            'permit_binding_sha256': '4' * 64,
            'prepared_target_sha256': '5' * 64,
            'started_worker_journal_sha256': '6' * 64,
            'fence_sha256': '7' * 64,
            'cohort_index': descendant,
            'handoff_state': (
                'CHECKPOINTED' if descendant == 0 else 'RUNNING'
            ),
            'cohort_quiescence_sha256': (
                '8' * 64 if descendant == 0 else None
            ),
        })
    observed = runner._binding_for_root(
        {'root_bindings': bindings}, roots[0],
    )
    assert observed['prepared_target_sha256'] == '5' * 64
    assert observed['started_worker_journal_sha256'] == '6' * 64
    with pytest.raises(
        runner.AdaptiveChildResumeError,
        match='handoff binding/session mismatch',
    ):
        runner._handoff_link_value(
            roots[0],
            {
                'selection': {
                    'global_leaf_index': observed['global_leaf_index'] + 1,
                    'descendant_index': observed['descendant_index'],
                    'descendant_sha256': observed['descendant_sha256'],
                },
            },
            {
                'record_sha256': observed['new_session_sha256'],
                'controller_start_sha256': observed[
                    'new_start_commit_sha256'
                ],
                'root_identity': observed['new_root_identity'],
            },
            tmp_path / 'unreached-handoff.json',
            {
                'record_sha256': '9' * 64,
                'attempt_id': 'a' * 64,
                'incident_precondition_sha256': 'b' * 64,
            },
            observed,
        )
    bad = json.loads(json.dumps(bindings))
    bad[0].pop('started_worker_journal_sha256')
    with pytest.raises(runner.AdaptiveChildResumeError, match='schema'):
        runner._binding_for_root({'root_bindings': bad}, roots[0])


@pytest.mark.parametrize(
    'binding_field',
    [
        'new_session_sha256',
        'new_start_commit_sha256',
    ],
)
def test_handoff_link_rejects_session_transport_cross_binding(
    tmp_path: Path, binding_field: str,
) -> None:
    root = tmp_path / 'cross-binding'
    static = {
        'selection': {
            'global_leaf_index': 100,
            'descendant_index': 0,
            'descendant_sha256': '1' * 64,
        },
    }
    session = {
        'record_sha256': '2' * 64,
        'controller_start_sha256': '3' * 64,
        'root_identity': {'path': str(root)},
    }
    binding = {
        'new_session_sha256': session['record_sha256'],
        'new_start_commit_sha256': session[
            'controller_start_sha256'
        ],
        'global_leaf_index': 100,
        'descendant_index': 0,
        'descendant_sha256': '1' * 64,
        'new_root_identity': session['root_identity'],
    }
    binding[binding_field] = 'f' * 64
    with pytest.raises(
        runner.AdaptiveChildResumeError,
        match='handoff binding/session mismatch',
    ):
        runner._handoff_link_value(
            root, static, session,
            tmp_path / 'unreached-handoff.json',
            {
                'record_sha256': '9' * 64,
                'attempt_id': 'a' * 64,
                'incident_precondition_sha256': 'b' * 64,
            },
            binding,
        )


def test_transferable_root_lock_close_preserves_adopted_flock(
    tmp_path: Path,
) -> None:
    root = tmp_path / 'transfer'
    root.mkdir(mode=0o700)
    root.chmod(0o700)
    runner._initialize_outer_lock(root)
    lock = runner._TransferableRootLock(root)
    lock.__enter__()
    adopted = os.dup(lock.fileno())
    lock.complete_transfer()
    lock.__exit__(None, None, None)
    probe = os.open(
        root / runner.ROOT_LOCK,
        os.O_RDWR | os.O_CLOEXEC | os.O_NOFOLLOW,
    )
    try:
        import fcntl
        with pytest.raises(BlockingIOError):
            fcntl.flock(probe, fcntl.LOCK_EX | fcntl.LOCK_NB)
        os.close(adopted)
        fcntl.flock(probe, fcntl.LOCK_EX | fcntl.LOCK_NB)
        fcntl.flock(probe, fcntl.LOCK_UN)
    finally:
        os.close(probe)


def _assert_transfer_locks_busy(
    locks: list[Any],
) -> None:
    import fcntl

    for lock in locks:
        probe = os.open(
            lock.root / runner.ROOT_LOCK,
            os.O_RDWR | os.O_CLOEXEC | os.O_NOFOLLOW,
        )
        try:
            with pytest.raises(BlockingIOError):
                fcntl.flock(
                    probe, fcntl.LOCK_EX | fcntl.LOCK_NB,
                )
        finally:
            os.close(probe)


def _assert_transfer_locks_released(
    locks: list[Any],
) -> None:
    import fcntl

    for lock in locks:
        probe = os.open(
            lock.root / runner.ROOT_LOCK,
            os.O_RDWR | os.O_CLOEXEC | os.O_NOFOLLOW,
        )
        try:
            fcntl.flock(probe, fcntl.LOCK_EX | fcntl.LOCK_NB)
            fcntl.flock(probe, fcntl.LOCK_UN)
        finally:
            os.close(probe)


@pytest.mark.parametrize("fail_at", range(8))
def test_outer_transfer_validation_fault_precedes_adoption_and_keeps_all_busy(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, fail_at: int,
) -> None:
    entries, _ = _atomic_entries(tmp_path)
    lease = _FakeLease()
    original = runner._TransferableRootLock.validated_transfer_fd
    calls = 0

    def injected_validation(lock: Any) -> int:
        nonlocal calls
        position = calls
        calls += 1
        if position == fail_at:
            raise RuntimeError("injected pre-adoption validation fault")
        return original(lock)

    monkeypatch.setattr(
        runner._TransferableRootLock,
        "validated_transfer_fd",
        injected_validation,
    )
    locks: list[Any] = []
    with contextlib.ExitStack() as stack:
        for entry in entries:
            runner._initialize_outer_lock(entry["root"])
            locks.append(stack.enter_context(
                runner._TransferableRootLock(entry["root"]),
            ))
        with pytest.raises(
            runner.AdaptiveChildResumeError,
            match="before continuous outer-lock adoption",
        ):
            runner._atomic_handoff_start(
                lease, entries,
                batch_commit_path=tmp_path / "commit.json",
                outer_locks=locks,
            )
        assert lease.adopted is None
        assert all(not lock._transferred for lock in locks)
        _assert_transfer_locks_busy(locks)
    _assert_transfer_locks_released(locks)


@pytest.mark.parametrize("fail_at", range(8))
def test_outer_transfer_close_fault_marks_all_before_close_and_never_unlocks(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, fail_at: int,
) -> None:
    entries, _ = _atomic_entries(tmp_path)

    class DuplicatingLease(_FakeLease):
        def __init__(self) -> None:
            super().__init__()
            self.duplicates: list[int] = []

        def adopt_prepared_outer_locks(
            self, *, outer_lock_fds: list[int],
        ) -> None:
            super().adopt_prepared_outer_locks(
                outer_lock_fds=outer_lock_fds,
            )
            self.duplicates = [
                os.dup(descriptor) for descriptor in outer_lock_fds
            ]

    lease = DuplicatingLease()
    locks: list[Any] = []
    original_fds: list[int] = []
    real_close = os.close
    with contextlib.ExitStack() as stack:
        for entry in entries:
            runner._initialize_outer_lock(entry["root"])
            lock = stack.enter_context(
                runner._TransferableRootLock(entry["root"]),
            )
            locks.append(lock)
            original_fds.append(lock.fileno())
        originals = set(original_fds)
        close_calls = 0

        def injected_close(descriptor: int) -> None:
            nonlocal close_calls
            if descriptor in originals:
                position = close_calls
                close_calls += 1
                if position == fail_at:
                    raise OSError(5, "injected adopted-close fault")
            real_close(descriptor)

        monkeypatch.setattr(runner.os, "close", injected_close)
        with pytest.raises(
            runner.AdaptiveChildResumeError,
            match="adopted caller descriptor close failed",
        ):
            runner._atomic_handoff_start(
                lease, entries,
                batch_commit_path=tmp_path / "commit.json",
                outer_locks=locks,
            )
        assert close_calls == 8
        assert lease.rollback is not None
        assert all(
            lock._transferred and lock._fd == -1 for lock in locks
        )
        _assert_transfer_locks_busy(locks)
    # ExitStack saw all eight wrappers as transferred and never LOCK_UNed.
    _assert_transfer_locks_busy(locks)
    monkeypatch.setattr(runner.os, "close", real_close)
    for descriptor in original_fds:
        with contextlib.suppress(OSError):
            real_close(descriptor)
    for descriptor in lease.duplicates:
        with contextlib.suppress(OSError):
            real_close(descriptor)
    _assert_transfer_locks_released(locks)


def _batch_entries(roots: list[Path]) -> list[dict[str, Any]]:
    return [
        {
            'root': root, 'cpu': lane, 'loaded': {'record': {'strict_base': True}},
            'lane_index': lane, 'descendant_index': descendant,
            'target_key': (lane, descendant),
        }
        for root, (lane, descendant) in zip(
            roots, runner.TARGET_KEYS, strict=True,
        )
    ]


def _install_batch_structure_fakes(
    monkeypatch: pytest.MonkeyPatch, roots: list[Path],
) -> None:
    monkeypatch.setattr(
        runner, '_cover_roots_cpus',
        lambda r, c: (list(r), list(c)),
    )
    monkeypatch.setattr(
        runner, '_root_lock',
        lambda *args, **kwargs: contextlib.nullcontext(),
    )
    monkeypatch.setattr(
        runner, '_temporary_cpu',
        lambda cpu: contextlib.nullcontext(),
    )
    monkeypatch.setattr(
        runner, '_load_static',
        lambda root, **kwargs: {'record': {'strict_base': True}},
    )
    monkeypatch.setattr(runner, '_batch_common', lambda loaded: {})
    monkeypatch.setattr(
        runner, '_cover_entries',
        lambda r, c, loaded: _batch_entries(list(r)),
    )
    monkeypatch.setattr(
        runner, '_verify_links_before_batch_mutation',
        lambda *args: None,
    )


def test_checkpoint_partial_commit_failure_same_command_retry_converges(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    tmp_path.chmod(0o700)
    roots = []
    for position in range(runner.COVER_ROOT_COUNT):
        root = tmp_path / f'batch-{position}'
        root.mkdir(mode=0o700)
        roots.append(root)
    cpus = [0, 1, 2, 3] * 2
    states = {root: 'RUNNING' for root in roots}
    incomplete: set[Path] = set()
    recovered: list[Path] = []
    failed = {'value': False}
    _install_batch_structure_fakes(monkeypatch, roots)
    monkeypatch.setattr(
        runner, '_last_action_is_incomplete',
        lambda root: root in incomplete,
    )
    monkeypatch.setattr(
        runner, '_recover_action_locked',
        lambda root: (
            incomplete.remove(root), recovered.append(root),
            runner.seal({'root': str(root)}),
        )[-1],
    )
    monkeypatch.setattr(
        runner, '_batch_preinspect',
        lambda root, cpu: runner.seal({
            'root': str(root), 'cpu': cpu, 'state': states[root],
        }),
    )

    def apply(root: Path, *, batch_token: Any) -> dict[str, Any]:
        del batch_token
        states[root] = 'CHECKPOINTED'
        if root == roots[5] and not failed['value']:
            failed['value'] = True
            incomplete.add(root)
            raise RuntimeError('post-action commit fault')
        return runner.seal({'root': str(root), 'goal': 'CHECKPOINTED'})

    monkeypatch.setattr(runner, '_checkpoint_stop_locked', apply)
    first = tmp_path / 'checkpoint-first.json'
    with pytest.raises(runner.AdaptiveChildResumeError, match='immutable summary'):
        runner._batch_action(
            'checkpoint-stop-batch', roots, cpus, summary_path=first,
        )
    assert first.exists() and states[roots[5]] == 'CHECKPOINTED'
    second = tmp_path / 'checkpoint-retry.json'
    result = runner._batch_action(
        'checkpoint-stop-batch', roots, cpus, summary_path=second,
    )
    assert result['success'] is True
    assert set(states.values()) == {'CHECKPOINTED'}
    assert recovered == [roots[5]] and roots[5] not in incomplete


@pytest.mark.parametrize("fault_mode", ["resume", "final-validation"])
def test_switch_cohort_failure_returns_global_zero_then_retry(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
    fault_mode: str,
) -> None:
    tmp_path.chmod(0o700)
    roots = []
    for position in range(runner.COVER_ROOT_COUNT):
        root = tmp_path / f'cohort-{position}'
        root.mkdir(mode=0o700)
        roots.append(root)
    cpus = [0, 1, 2, 3] * 2
    states = {
        root: ('RUNNING' if position < runner.COHORT_SIZE else 'CHECKPOINTED')
        for position, root in enumerate(roots)
    }
    failed = {'value': False}
    _install_batch_structure_fakes(monkeypatch, roots)
    monkeypatch.setattr(
        runner, '_last_action_is_incomplete', lambda root: False,
    )
    def inspect(root: Path, cpu: int) -> dict[str, Any]:
        observed = states[root]
        if (
            fault_mode == 'final-validation'
            and not failed['value']
            and root == roots[-1]
            and all(
                states[item] == 'RUNNING'
                for item in roots[runner.COHORT_SIZE:]
            )
        ):
            failed['value'] = True
            observed = 'CHECKPOINTED'
        return runner.seal({
            'root': str(root), 'cpu': cpu, 'state': observed,
        })

    monkeypatch.setattr(runner, '_batch_preinspect', inspect)
    monkeypatch.setattr(
        runner, '_checkpoint_stop_locked',
        lambda root, *, batch_token: (
            states.__setitem__(root, 'CHECKPOINTED'),
            runner.seal({'root': str(root)}),
        )[-1],
    )
    monkeypatch.setattr(
        runner, '_global_zero_quiescence_record',
        lambda root, lane, descendant, loaded: (
            (_ for _ in ()).throw(RuntimeError('still live'))
            if states[root] == 'RUNNING'
            else runner.seal({
                'lane_index': lane, 'descendant_index': descendant,
                'root': str(root),
            })
        ),
    )

    def resume(root: Path, *, batch_token: Any) -> dict[str, Any]:
        position = roots.index(root)
        states[root] = 'RUNNING'
        if (
            fault_mode == 'resume'
            and position == runner.COHORT_SIZE + 2
            and not failed['value']
        ):
            failed['value'] = True
            states[root] = 'CHECKPOINTED'
            raise runner._PostSpawnFailure(
                'resume admission fault',
                runner.seal({'root': str(root), 'quiescent': True}),
            )
        return runner.seal({
            'controller_result': controller.seal_manifest(
                'resume.commit', {
                    'pid': 700000 + position,
                    'proc_start_ticks': 800000 + position,
                },
            ),
        })

    def stop(
        root: Path, started: Mapping[str, Any], *,
        lane_index: int | None, descendant_index: int | None = None,
    ) -> dict[str, Any]:
        del started, lane_index, descendant_index
        states[root] = 'CHECKPOINTED'
        return runner.seal({'root': str(root), 'quiescent': True})

    monkeypatch.setattr(runner, '_resume_locked', resume)
    monkeypatch.setattr(runner, '_stop_failed_new_root', stop)
    first = tmp_path / 'switch-first.json'
    with pytest.raises(runner.AdaptiveChildResumeError, match='immutable summary'):
        runner.switch_cohort_batch(
            roots, cpus, descendant_index=1, summary_path=first,
        )
    assert set(states.values()) == {'CHECKPOINTED'}
    failed_summary = json.loads(first.read_text())
    assert failed_summary['success'] is False
    assert failed_summary['post_failure_global_zero_sha256']
    assert len(
        failed_summary['post_failure_quiescence_record_sha256s']
    ) == runner.COVER_ROOT_COUNT
    second = tmp_path / 'switch-retry.json'
    result = runner.switch_cohort_batch(
        roots, cpus, descendant_index=1, summary_path=second,
    )
    assert result['success'] is True
    assert [
        states[root] for root in roots
    ] == ['CHECKPOINTED'] * 4 + ['RUNNING'] * 4


def test_bad_summary_and_handoff_link_preflight_have_zero_transport_side_effect(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    tmp_path.chmod(0o700)
    roots = []
    for lane in range(runner.COVER_ROOT_COUNT):
        root = tmp_path / f'root-{lane}'
        root.mkdir(mode=0o700)
        (root / 'state').mkdir(mode=0o700)
        roots.append(root)
    calls: list[str] = []
    monkeypatch.setattr(runner, '_cover_roots_cpus', lambda r, c: (list(r), list(c)))
    monkeypatch.setattr(runner, '_batch_preinspect', lambda *args: calls.append('inspect'))
    existing = tmp_path / 'existing-summary.json'
    existing.write_text('{}')
    with pytest.raises(runner.AdaptiveChildResumeError, match='must be new'):
        runner._batch_action('checkpoint-stop-batch', roots, [0, 1, 2, 3] * 2, summary_path=existing)
    assert calls == []
    (roots[2] / runner.HANDOFF_LINK).symlink_to(tmp_path / 'absent')
    monkeypatch.setattr(runner, '_load_static', lambda *args, **kwargs: calls.append('load'))
    with pytest.raises(runner.AdaptiveChildResumeError, match='root handoff link'):
        runner.start_batch(
            roots, [0, 1, 2, 3] * 2, batch_commit_path=tmp_path / 'batch-commit.json',
            expected_incident_precondition_sha256='1' * 64,
            instance=TEST_INSTANCE, switch_verifier=_switch_verifier,
            science_modules=SCIENCE, lease_factory=lambda *args, **kwargs: None,
        )
    assert calls == []


@pytest.mark.parametrize('operation', ['checkpoint', 'resume', 'harvest', 'verify'])
def test_strict_missing_handoff_link_blocks_transport_and_terminal(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, operation: str,
) -> None:
    root = tmp_path / operation
    root.mkdir(mode=0o700)
    runner._initialize_outer_lock(root)
    fake_loaded = {'record': {'strict_base': True, 'record_sha256': '1' * 64}}
    fake_session = {'record_sha256': '2' * 64, 'expected_single_cpu': 0}
    monkeypatch.setattr(runner, '_load_static', lambda *args, **kwargs: fake_loaded)
    monkeypatch.setattr(runner, '_load_session', lambda *args, **kwargs: fake_session)
    monkeypatch.setattr(runner, '_inspect_controller', lambda *args: (_ for _ in ()).throw(AssertionError('transport touched')))
    function = {
        'checkpoint': runner.checkpoint_stop_root,
        'resume': runner.resume_root,
        'harvest': runner.harvest_root,
        'verify': runner.verify_root,
    }[operation]
    with pytest.raises(runner.AdaptiveChildResumeError):
        function(root)
    assert not (root / runner.TERMINAL_CLAIM).exists()


@pytest.mark.parametrize(
    "fault_name", [runner.CERTIFICATE.name, runner.FINAL_COMMIT.name],
)
def test_terminal_bundle_publish_fault_leaves_checkpoint_resumable(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
    fault_name: str,
) -> None:
    root, _ = _prepare(tmp_path)
    transport = _FakeTransport(monkeypatch)
    runner.start_root(root, **_action_kwargs())
    _install_real_tiny_proof(root)
    transport.state = "CHECKPOINTED"
    transport.checkpoint = controller.seal_manifest(
        "checkpoint.commit", {"generation": 0},
    )
    real_publish_json = runner._publish_json

    def fault_publish(path: Path, value: Mapping[str, Any]) -> None:
        if (
            path.parent.name.startswith(
                runner.TERMINAL_STAGING_PREFIX
            )
            and path.name == fault_name
        ):
            raise OSError(f"injected publish fault: {fault_name}")
        real_publish_json(path, value)

    monkeypatch.setattr(runner, "_publish_json", fault_publish)
    with pytest.raises(OSError, match="injected publish fault"):
        runner.harvest_root(root, **_action_kwargs())
    assert not (root / runner.TERMINAL_BUNDLE).exists()
    assert not (root / runner.TERMINAL_CLAIM).exists()
    assert not any(
        item.name.startswith(runner.TERMINAL_STAGING_PREFIX)
        for item in root.iterdir()
    )
    assert transport.state == "CHECKPOINTED"
    resumed = runner.resume_root(root, **_action_kwargs())
    assert resumed["transition"] == "RESUMED_RUNNING"


def test_terminal_bundle_rename_fault_leaves_checkpoint_resumable(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    root, _ = _prepare(tmp_path)
    transport = _FakeTransport(monkeypatch)
    runner.start_root(root, **_action_kwargs())
    _install_real_tiny_proof(root)
    transport.state = "CHECKPOINTED"
    transport.checkpoint = controller.seal_manifest(
        "checkpoint.commit", {"generation": 0},
    )
    real_rename = runner.os.rename

    def fail_terminal_rename(
        source: Any, destination: Any, *args: Any, **kwargs: Any,
    ) -> None:
        if Path(destination) == root / runner.TERMINAL_BUNDLE:
            raise OSError("injected terminal rename fault")
        real_rename(source, destination, *args, **kwargs)

    monkeypatch.setattr(runner.os, "rename", fail_terminal_rename)
    with pytest.raises(OSError, match="terminal rename fault"):
        runner.harvest_root(root, **_action_kwargs())
    assert not (root / runner.TERMINAL_BUNDLE).exists()
    assert not any(
        item.name.startswith(runner.TERMINAL_STAGING_PREFIX)
        for item in root.iterdir()
    )
    assert runner.resume_root(root, **_action_kwargs())[
        "transition"
    ] == "RESUMED_RUNNING"


def test_orphan_precommit_terminal_staging_is_non_authoritative_and_retryable(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    root, _ = _prepare(tmp_path)
    transport = _FakeTransport(monkeypatch)
    runner.start_root(root, **_action_kwargs())
    _install_real_tiny_proof(root)
    transport.state = "CHECKPOINTED"
    transport.checkpoint = controller.seal_manifest(
        "checkpoint.commit", {"generation": 0},
    )
    orphan = root / f"{runner.TERMINAL_STAGING_PREFIX}crash"
    orphan.mkdir(mode=0o700)
    (orphan / runner.TERMINAL_CLAIM.name).write_bytes(
        b"non-authoritative crash debris\n"
    )
    resumed = runner.resume_root(root, **_action_kwargs())
    assert resumed["transition"] == "RESUMED_RUNNING"
    stopped = runner.checkpoint_stop_root(root, **_action_kwargs())
    assert stopped["transition"] == "CHECKPOINTED_STOPPED"
    final = runner.harvest_root(root, **_action_kwargs())
    assert final["leaf_unsat_authenticated"] is True
    assert orphan.exists()
    bundle = root / runner.TERMINAL_BUNDLE
    assert bundle.is_dir()
    assert {item.name for item in bundle.iterdir()} == (
        runner.TERMINAL_BUNDLE_FILES
    )
    assert runner.verify_root(root, **_action_kwargs())["valid"] is True


def test_terminal_certificate_and_final_reseal_are_rejected(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    root, _ = _prepare(tmp_path)
    transport = _FakeTransport(monkeypatch)
    runner.start_root(root, **_action_kwargs())
    _install_real_tiny_proof(root)
    transport.state = "INACTIVE_UNCHECKPOINTED"
    runner.harvest_root(root, **_action_kwargs())
    cert_path = root / runner.CERTIFICATE
    final_path = root / runner.FINAL_COMMIT
    original_cert = runner._read_json(cert_path, root=root)
    original_final = runner._read_json(final_path, root=root)

    altered_cert = dict(original_cert)
    altered_cert.pop("record_sha256")
    altered_cert["global_leaf_index"] += 1
    altered_cert = runner.seal(altered_cert)
    altered_final = dict(original_final)
    altered_final.pop("record_sha256")
    altered_final["certificate_sha256"] = altered_cert["record_sha256"]
    altered_final = runner.seal(altered_final)
    cert_path.write_bytes(runner.canonical_bytes(altered_cert) + b"\n")
    final_path.write_bytes(runner.canonical_bytes(altered_final) + b"\n")
    with pytest.raises(
        runner.AdaptiveChildResumeError,
        match="certificate canonical binding",
    ):
        runner.verify_root(root, **_action_kwargs())

    cert_path.write_bytes(runner.canonical_bytes(original_cert) + b"\n")
    final_path.write_bytes(runner.canonical_bytes(original_final) + b"\n")
    altered_final = dict(original_final)
    altered_final.pop("record_sha256")
    altered_final["descendant_index"] = 1
    altered_final = runner.seal(altered_final)
    final_path.write_bytes(runner.canonical_bytes(altered_final) + b"\n")
    with pytest.raises(
        runner.AdaptiveChildResumeError,
        match="final record canonical binding",
    ):
        runner.verify_root(root, **_action_kwargs())


@pytest.mark.parametrize(
    "missing_name", [runner.TERMINAL_CLAIM.name, runner.FINAL_COMMIT.name],
)
def test_fixed_terminal_bundle_remains_fail_closed_if_inner_file_is_missing(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
    missing_name: str,
) -> None:
    root, _ = _prepare(tmp_path)
    transport = _FakeTransport(monkeypatch)
    runner.start_root(root, **_action_kwargs())
    _install_real_tiny_proof(root)
    transport.state = "CHECKPOINTED"
    transport.checkpoint = controller.seal_manifest(
        "checkpoint.commit", {"generation": 0},
    )
    runner.harvest_root(root, **_action_kwargs())
    (root / runner.TERMINAL_BUNDLE / missing_name).unlink()
    with pytest.raises(
        runner.AdaptiveChildResumeError, match="terminal stage",
    ):
        runner.resume_root(root, **_action_kwargs())
    with pytest.raises((OSError, runner.AdaptiveChildResumeError)):
        runner.verify_root(root, **_action_kwargs())


def test_tiny_unsat_fresh_drat_lrat_replay_tamper_and_fake_marker(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    root, _ = _prepare(tmp_path)
    transport = _FakeTransport(monkeypatch)
    runner.start_root(root, **_action_kwargs())
    _install_real_tiny_proof(root)
    transport.state = 'INACTIVE_UNCHECKPOINTED'
    final = runner.harvest_root(root, **_action_kwargs())
    assert final['leaf_unsat_authenticated'] is True
    bundle = root / runner.TERMINAL_BUNDLE
    assert bundle.is_dir()
    assert {item.name for item in bundle.iterdir()} == (
        runner.TERMINAL_BUNDLE_FILES
    )
    verification = runner.verify_root(root, **_action_kwargs())
    assert verification['valid'] is True
    with (root / runner.DRAT_ARTIFACT).open('ab') as stream:
        stream.write(b'tamper')
    with pytest.raises(runner.AdaptiveChildResumeError, match='artifact binding'):
        runner.verify_root(root, **_action_kwargs())

    fake_parent = tmp_path / 'fake-marker'
    fake_parent.mkdir(mode=0o700)
    fake_root, _ = _prepare(fake_parent)
    fake_transport = _FakeTransport(monkeypatch)
    runner.start_root(fake_root, **_action_kwargs())
    runtime = fake_root / runner.RUNTIME_ROOT
    (runtime / 'proof.drat').write_bytes(b'not-a-proof\n')
    (runtime / 'solver.stdout').write_bytes(b's UNSATISFIABLE\n')
    fake_transport.state = 'CHECKPOINTED'
    fake_transport.checkpoint = controller.seal_manifest('checkpoint.commit', {'generation': 0})
    with pytest.raises(runner.AdaptiveChildResumeError, match='checker failed'):
        runner.harvest_root(fake_root, **_action_kwargs())
    assert not (fake_root / runner.TERMINAL_CLAIM).exists()
    resumed = runner.resume_root(fake_root, **_action_kwargs())
    assert resumed['transition'] == 'RESUMED_RUNNING'


def test_cli_replay_scope_reuses_only_within_one_invocation(tmp_path: Path) -> None:
    material = _materials()
    batch_root = _batch_root(tmp_path)
    _ScopedFakeOverlay.full_replays = 0
    _ScopedFakeOverlay.local_replays = 0
    _ScopedFakeOverlay.last_token = None
    switch_calls = {'count': 0}

    def counted_switch(record: Mapping[str, Any]) -> dict[str, Any]:
        switch_calls['count'] += 1
        return _switch_verifier(record)

    def invoke(descendant_index: int) -> dict[str, Any]:
        return runner._fresh_target(
            parent=material['parent'], width6=material['width6'],
            width10=material['width10'],
            overlay_manifest=material['overlay'],
            hard_evidence=material['hard'],
            switch_evidence=material['switch'], batch_root=batch_root,
            expected_overlay_sha256=material['overlay']['manifest_sha256'],
            expected_hard_evidence_sha256=material['hard']['evidence_sha256'],
            expected_switch_evidence_sha256=material['switch']['record_sha256'],
            expected_batch_manifest_sha256=BATCH_PIN,
            descendant_index=descendant_index, candidate_variables=[1],
            timeout_seconds=60.0,
            elapsed_seconds_by_lane=[60.1, 60.2, 60.3, 60.4],
            instance=TEST_INSTANCE, strict_base=False,
            switch_verifier=counted_switch, science_modules=SCOPED_SCIENCE,
        )

    with runner._cli_replay_scope():
        first = invoke(0)
        second = invoke(1)
        state = runner._active_cli_replay_scope()
        token = _ScopedFakeOverlay.last_token
        assert first['child_payload'] != second['child_payload']
        assert _ScopedFakeOverlay.full_replays == 1
        assert _ScopedFakeOverlay.local_replays == 1
        assert switch_calls['count'] == 1
        assert len(state['overlay_cache']) == 1
        assert len(state['switch_cache']) == 1
        assert token.active is True
    assert token.active is False
    assert getattr(runner._CLI_REPLAY_LOCAL, 'state', None) is None

    with runner._cli_replay_scope():
        invoke(0)
        second_token = _ScopedFakeOverlay.last_token
        assert second_token is not token
        assert second_token.active is True
        assert _ScopedFakeOverlay.full_replays == 2
        assert _ScopedFakeOverlay.local_replays == 2
        assert switch_calls['count'] == 2
    assert second_token.active is False
    assert getattr(runner._CLI_REPLAY_LOCAL, 'state', None) is None


def test_strict_python_gate_and_cli_surface() -> None:
    with pytest.raises(runner.AdaptiveChildResumeError, match='-I -S -B'):
        runner._python_startup_binding(True)
    choices = runner.build_parser()._subparsers._group_actions[0].choices
    assert {
        'prepare', 'start-batch', 'checkpoint-stop-batch', 'resume-batch',
        'status-batch', 'switch-cohort-batch', 'recover-action',
        'repair-handoff-links',
        'inspect-incident-batch',
        'rollback-handoff-batch', 'harvest', 'verify',
    } <= set(choices)
    source = DRAFT.read_text()
    assert 'run_paper400_dic5_adaptive_child_resume_v1' not in source
    assert 'run_paper400_dic5_adaptive_child_resume_v2' not in source
    assert 'run_paper400_dic5_adaptive_child_resume_v3' not in source
    assert 'run_paper400_dic5_adaptive_child_resume_v4' not in source
    assert 'monkeypatch' not in source
    assert 'addsitedir' not in source
    assert runner._STRICT_DEPENDENCY_ROOT == Path(
        '/root/qcode-stage3-distqldpc-lower-v1/qcode-discovery/.venv/'
        'lib/python3.12/site-packages'
    )


def _strict_subprocess_source(*, full_probe: bool) -> str:
    setup = (
        "import hashlib,json,pathlib,sys,types\n"
        f"path=pathlib.Path({str(DRAFT)!r})\n"
        "runner=types.ModuleType("
        "'scripts.run_paper400_dic5_adaptive_child_resume_v5')\n"
        "runner.__file__=str(path)\n"
        "runner.__package__='scripts'\n"
        "runner.__loader__=None\n"
        "runner.__spec__=None\n"
        "sys.modules[runner.__name__]=runner\n"
        "exec(compile(path.read_bytes(),str(path),'exec',dont_inherit=True),"
        "runner.__dict__)\n"
    )
    if not full_probe:
        return setup + (
            "try:\n"
            " runner.main([])\n"
            "except runner.AdaptiveChildResumeError as exc:\n"
            " print(str(exc))\n"
            " raise SystemExit(0)\n"
            "raise SystemExit(9)\n"
        )
    return setup + (
        "before=list(sys.path)\n"
        "result={}\n"
        "def probe(argv):\n"
        " state=runner._active_strict_dependency_context()\n"
        " result['pycache_path']=state['pycache_path']\n"
        " switch=runner._switch_v4_module("
        "runner._SWITCH_V4_SOURCE_SHA256)\n"
        " _,overlay_source,overlay_executed=switch._load_overlay_exact()\n"
        " serialized_overlay_source=dict(overlay_source)\n"
        " serialized_overlay_source['execution']='compile-exact-source-bytes-v3'\n"
        " runner._adopt_strict_derived_environment(overlay_executed)\n"
        " binding=switch.base._source_binding("
        "{'legacy_project':str(runner.PROJECT),'legacy_sources':[]},"
        "[],serialized_overlay_source,overlay_executed)\n"
        " record={'source_binding':binding}\n"
        " modules=runner._science_modules(record)\n"
        " assert runner._science_modules(record)==modules\n"
        " instance=runner._strict_scoped_instance(modules)\n"
        " fingerprint=modules[0]._instance_replay_fingerprint("
        "instance,strict_base=True)\n"
        " result['instance_fingerprint']={'bytes':len(fingerprint),"
        "'sha256':hashlib.sha256(fingerprint).hexdigest()}\n"
        " startup=runner._python_startup_binding(True)\n"
        " execution=runner._execution_module_binding("
        "modules,record,strict_base=True)\n"
        " result['startup']=startup\n"
        " result['execution']=execution\n"
        " result['strict_sys_path']=list(sys.path)\n"
        " result['numpy_version']=sys.modules['numpy'].__version__\n"
        " result['forbidden_inside']=sorted("
        "set(sys.modules).intersection("
        "runner._STRICT_FORBIDDEN_STARTUP_MODULES))\n"
        " return 0\n"
        "runner._main_in_cli_replay_scope=probe\n"
        "assert runner.main([])==0\n"
        "assert sys.path==before\n"
        "assert getattr(runner._STRICT_DEPENDENCY_LOCAL,'state',None) is None\n"
        "assert not pathlib.Path(result['pycache_path']).exists()\n"
        "result.pop('pycache_path')\n"
        "result['forbidden_after']=sorted(set(sys.modules).intersection("
        "runner._STRICT_FORBIDDEN_STARTUP_MODULES))\n"
        "result['native_environment_after']="
        "runner._strict_environment_snapshot()\n"
        "result['process_environment_after']="
        "runner._strict_process_environment_snapshot()\n"
        "print(json.dumps(result,sort_keys=True))\n"
    )


def _strict_subprocess_environment() -> dict[str, str]:
    return dict(runner._STRICT_ENTRY_ENVIRONMENT)


_REAL_PREPARE_MATERIALS = Path(os.environ.get(
    'PAPER400_REAL_PREPARE_MATERIALS',
    '/root/paper400-adaptive-prod-20260827-mHCpDT/materials-000001',
))
_REAL_PREPARE_BATCH_ROOT = Path(os.environ.get(
    'PAPER400_REAL_PREPARE_BATCH_ROOT',
    '/tmp/paper400-dic5-width10-parent000-batch000-v3-b59cfbe9-20260827T054227Z',
))


def _real_prepare_cli_argv(
    root: Path, *, materials: Path = _REAL_PREPARE_MATERIALS,
) -> list[str]:
    return [
        str(runner._STRICT_PYTHON), '-I', '-S', '-B', str(DRAFT), 'prepare',
        '--root', str(root),
        '--batch-root', str(_REAL_PREPARE_BATCH_ROOT),
        '--parent-manifest', str(materials / 'parent-manifest.json'),
        '--width6-campaign', str(materials / 'width6-campaign.json'),
        '--width10-campaign', str(materials / 'width10-campaign.json'),
        '--overlay-manifest', str(materials / 'lane-0/overlay.json'),
        '--hard-evidence', str(materials / 'lane-0/hard-evidence.json'),
        '--switch-evidence', str(materials / 'switch-evidence.json'),
        '--elapsed-seconds-by-lane-json',
        str(materials / 'elapsed-seconds-by-lane.json'),
        '--expected-overlay-sha256',
        '5d6af396290361eed58a1ae7066ac4a2abfd2e3b0260afd39ac8787b39d03acf',
        '--expected-hard-evidence-sha256',
        '4b44152fa91e706dadc1b5b573618e0e724d896bca81f3a352fb5f1559b7b95c',
        '--expected-switch-evidence-sha256',
        '2ac95f8d035f0edf604077a2cd1d0db837b1d457704eb18e0777c09f33e80c7b',
        '--expected-batch-manifest-sha256',
        '3228c3dab9464efd656eda26301ea200074085c08eedfb6abd19d2f683cfe40f',
        '--descendant-index', '0',
        '--candidate-variable', '390',
        '--timeout-seconds', '86400',
        '--proof-max-bytes', '68719476736',
    ]


def test_real_isolated_dependency_context_and_science_execution_binding() -> None:
    observations: list[dict[str, Any]] = []
    for _ in range(2):
        completed = subprocess.run(
            [
                str(runner._STRICT_PYTHON), '-I', '-S', '-B', '-c',
                _strict_subprocess_source(full_probe=True),
            ],
            cwd=PROJECT, env=_strict_subprocess_environment(),
            stdin=subprocess.DEVNULL, stdout=subprocess.PIPE,
            stderr=subprocess.PIPE, timeout=240, check=False,
        )
        assert completed.returncode == 0, completed.stderr.decode(
            'utf-8', 'replace',
        )
        observations.append(json.loads(completed.stdout))
    assert observations[0] == observations[1]
    observed = observations[0]
    assert observed['forbidden_inside'] == []
    assert observed['forbidden_after'] == []
    assert observed['native_environment_after'] == {}
    assert observed['process_environment_after'] == dict(
        runner._STRICT_ENTRY_ENVIRONMENT
    )
    assert observed['numpy_version'] == '2.3.5'
    assert observed['strict_sys_path'] == [
        str(PROJECT), '/usr/lib/python3.12',
        '/usr/lib/python3.12/lib-dynload',
        str(runner._STRICT_DEPENDENCY_ROOT),
    ]
    startup = observed['startup']
    execution = observed['execution']
    assert startup['isolated'] is startup['no_site'] is True
    assert startup['dont_write_bytecode'] is startup['safe_path'] is True
    assert startup['strict_runtime_binding']['sys_executable'] == str(
        runner._STRICT_PYTHON
    )
    assert startup['strict_runtime_binding']['python_sha256'] == (
        runner._STRICT_PYTHON_SHA256
    )
    assert startup['strict_runtime_binding']['pyvenv_cfg_sha256'] == (
        runner._STRICT_PYVENV_CFG_SHA256
    )
    dependency = runner._expected_strict_dependency_tree()
    assert dependency['numba_cache_file_count'] == 8
    assert dependency['numba_cache_bytes'] == 127448
    assert dependency['numba_cache_sha256'] == (
        runner._STRICT_DEPENDENCY_EXPECTED_NUMBA_CACHE_SHA256
    )
    assert 'including-pyc-and-cache-subtrees' in dependency['coverage']
    assert startup['dependency_tree'] == dependency
    assert execution['dependency_tree'] == dependency
    stdlib = runner._expected_strict_stdlib_tree()
    assert stdlib['symlinks'] == [
        {'relative_path': relative, 'target': target}
        for relative, target in runner._STRICT_STDLIB_EXPECTED_SYMLINK_RECORDS
    ]
    assert startup['system_stdlib_tree'] == stdlib
    assert execution['system_stdlib_tree'] == stdlib
    external = execution['stdlib_external_symlink_targets']
    assert {item['path'] for item in external['files']} == {
        '/etc/python3.12/sitecustomize.py',
        '/usr/lib/x86_64-linux-gnu/libpython3.12.so.1.0',
    }
    assert execution['science_derived_environment']['environment'] == {
        key: value for key, value in runner._STRICT_DERIVED_THREAD_ENV
    }
    assert execution['science_derived_environment']['entry_environment'] == dict(
        runner._STRICT_ENTRY_ENVIRONMENT
    )
    assert execution['science_derived_environment']['effective_environment'] == {
        **dict(runner._STRICT_ENTRY_ENVIRONMENT),
        **dict(runner._STRICT_DERIVED_THREAD_ENV),
    }
    writer = execution['science_derived_environment']['writer_source']
    assert writer == runner._expected_strict_derived_env_writer_record()
    assert writer['module'] == runner._STRICT_DERIVED_ENV_WRITER_MODULE
    assert writer['path'] == str(runner._STRICT_DERIVED_ENV_WRITER)
    assert writer['sha256'] == runner._STRICT_DERIVED_ENV_WRITER_SHA256
    assert writer['execution'] == 'compile-exact-source-bytes-v4'
    assert execution['science_derived_environment'][
        'effect_scope'
    ] == 'sets-listed-keys-before-lower-final-v5-own-numpy-and-qldpc-imports-v1'
    assert execution['optimized_instance_fingerprint'] == (
        observed['instance_fingerprint']
    )
    mapped = execution['mapped_runtime_closure']
    assert mapped['proc_self_exe']['path'] == '/usr/bin/python3.12'
    assert mapped['system_manifest_frozen_in_source'] is True
    assert mapped['summaries']['system'] == {
        'file_count': runner._STRICT_SYSTEM_MAP_EXPECTED_FILES,
        'bytes': runner._STRICT_SYSTEM_MAP_EXPECTED_BYTES,
        'files_sha256': runner._STRICT_SYSTEM_MAP_EXPECTED_SHA256,
    }
    expected_system_files = [
        {
            'path': path, 'bytes': size, 'sha256': sha256,
            'uid': uid, 'mode': mode, 'links': links,
        }
        for path, size, sha256, uid, mode, links
        in runner._STRICT_SYSTEM_MAP_EXPECTED_RECORDS
    ]
    assert mapped['system_files'] == expected_system_files
    assert not {
        '/usr/lib/locale/C.utf8/LC_CTYPE',
        '/usr/lib/locale/locale-archive',
        '/usr/lib/x86_64-linux-gnu/gconv/gconv-modules.cache',
    }.intersection(item['path'] for item in mapped['system_files'])
    assert mapped['anonymous_executable']['count_method'] == (
        'nonempty-permission-classes-v1'
    )
    assert mapped['anonymous_executable']['count'] == 2
    assert mapped['anonymous_executable']['bytes'] == 90112
    assert mapped['anonymous_executable'][
        'raw_vma_boundaries_recorded'
    ] is False
    assert execution['persistent_change_detection'] is True
    assert execution['privileged_toctou_defended'] is False
    assert execution['switch_v2_source_sha256'] == (
        runner._SWITCH_V2_SOURCE_SHA256
    )
    assert execution['switch_v4_source_sha256'] == (
        runner._SWITCH_V4_SOURCE_SHA256
    )
    assert runner.canonical_sha256({
        key: value for key, value in execution.items()
        if key != 'execution_module_binding_sha256'
    }) == execution['execution_module_binding_sha256']


@pytest.mark.slow
@pytest.mark.skipif(
    os.environ.get('PAPER400_RUN_REAL_PREPARE') != '1',
    reason='requires explicitly gated immutable production materials',
)
def test_real_prepare_cli_uses_exact_entry_environment_and_17_file_closure(
    tmp_path: Path,
) -> None:
    root = tmp_path / 'root'
    completed = subprocess.run(
        _real_prepare_cli_argv(root),
        cwd=PROJECT, env=_strict_subprocess_environment(),
        stdin=subprocess.DEVNULL, stdout=subprocess.PIPE,
        stderr=subprocess.PIPE, timeout=300, check=False,
    )
    assert completed.returncode == 0, completed.stderr.decode(
        'utf-8', 'replace',
    )
    static = json.loads((root / 'state/00-static.json').read_bytes())
    assert completed.stdout == runner.canonical_bytes(static) + b'\n'
    assert static['state'] == 'RESUMABLE_STATIC_SEALED'
    assert runner.canonical_sha256({
        key: value for key, value in static.items() if key != 'record_sha256'
    }) == static['record_sha256']
    launch = static['python_startup']['strict_runtime_binding']['launch_inputs']
    assert launch['entry_environment'] == dict(runner._STRICT_ENTRY_ENVIRONMENT)
    derived = static['execution_module_binding']['science_derived_environment']
    assert derived['entry_environment'] == dict(runner._STRICT_ENTRY_ENVIRONMENT)
    assert derived['effective_environment'] == {
        **dict(runner._STRICT_ENTRY_ENVIRONMENT),
        **dict(runner._STRICT_DERIVED_THREAD_ENV),
    }
    mapped = static['execution_module_binding']['mapped_runtime_closure']
    expected_system_files = [
        {
            'path': path, 'bytes': size, 'sha256': sha256,
            'uid': uid, 'mode': mode, 'links': links,
        }
        for path, size, sha256, uid, mode, links
        in runner._STRICT_SYSTEM_MAP_EXPECTED_RECORDS
    ]
    assert mapped['system_files'] == expected_system_files
    assert mapped['summaries']['system'] == {
        'file_count': 17,
        'bytes': 14576760,
        'files_sha256':
            '8f635d72d68f1dcd88cf0c9a9a019b8cb0ff65e0bf1e4379a8ec4e3cf1935d49',
    }
    assert not {
        '/usr/lib/locale/C.utf8/LC_CTYPE',
        '/usr/lib/locale/locale-archive',
        '/usr/lib/x86_64-linux-gnu/gconv/gconv-modules.cache',
    }.intersection(item['path'] for item in mapped['system_files'])
    assert static['source_binding']['sources'][
        'adaptive_child_runner_v5_source'
    ]['sha256'] == hashlib.sha256(DRAFT.read_bytes()).hexdigest()


def test_real_prepare_cli_rejects_c_utf8_before_material_io(
    tmp_path: Path,
) -> None:
    root = tmp_path / 'root'
    missing_materials = tmp_path / 'materials-that-must-not-be-read'
    environment = _strict_subprocess_environment()
    environment['LANG'] = 'C.UTF-8'
    completed = subprocess.run(
        _real_prepare_cli_argv(root, materials=missing_materials),
        cwd=PROJECT, env=environment, stdin=subprocess.DEVNULL,
        stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=30,
        check=False,
    )
    assert completed.returncode == 2
    assert completed.stdout == b''
    assert (
        'strict entry process environment differs from exact pin'
        in completed.stderr.decode('utf-8', 'strict')
    )
    assert not root.exists()
    assert not missing_materials.exists()


@pytest.mark.parametrize(
    'flags,environment_name,environment_value',
    [
        (['-I', '-S'], None, None),
        (['-S', '-B'], None, None),
        (['-I', '-S', '-B'], 'LD_LIBRARY_PATH', '/tmp'),
        (['-I', '-S', '-B'], 'NUMBA_CACHE_DIR', '/tmp'),
        (['-I', '-S', '-B'], 'OPENBLAS_NUM_THREADS', '/tmp'),
        (['-I', '-S', '-B'], 'LANG', 'C.UTF-8'),
        (['-I', '-S', '-B'], 'LC_ALL', 'C.UTF-8'),
        (['-I', '-S', '-B'], 'LC_CTYPE', 'C.UTF-8'),
        (['-I', '-S', '-B'], 'PATH', '/usr/bin:/bin'),
        (['-I', '-S', '-B'], 'HOME', '/root'),
        (['-I', '-S', '-B'], 'PYTHONPATH', '/tmp/test-only-imports'),
        (['-I', '-S', '-B'], 'LANG', None),
        (['-I', '-S', '-B'], 'LC_ALL', None),
        (['-I', '-S', '-B'], 'TZ', None),
    ],
)
def test_strict_subprocess_rejects_wrong_flags_and_loader_environment(
    flags: list[str],
    environment_name: str | None,
    environment_value: str | None,
) -> None:
    environment = _strict_subprocess_environment()
    if environment_name is not None:
        if environment_value is None:
            environment.pop(environment_name)
        else:
            environment[environment_name] = environment_value
    completed = subprocess.run(
        [
            str(runner._STRICT_PYTHON), *flags, '-c',
            _strict_subprocess_source(full_probe=False),
        ],
        cwd=PROJECT, env=environment, stdin=subprocess.DEVNULL,
        stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=30,
        check=False,
    )
    assert completed.returncode == 0, completed.stderr.decode(
        'utf-8', 'replace',
    )
    output = completed.stdout.decode('utf-8', 'strict')
    if environment_name is None:
        assert '-I -S -B' in output
    else:
        assert 'strict entry process environment differs from exact pin' in output


def test_numba_config_and_proc_maps_fail_closed(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    config = tmp_path / '.numba_config.yaml'
    runner._require_absent_numba_config(config)
    config.write_text('cache_dir: /tmp/escape\n', encoding='ascii')
    with pytest.raises(runner.AdaptiveChildResumeError, match='numba_config'):
        runner._require_absent_numba_config(config)

    observed = runner._parse_proc_maps(
        b'00001000-00002000 r-xp 00000000 00:00 0\n'
        b'00002000-00003000 rw-s 00000000 00:01 2 '
        b'/dev/shm/sem.Ab12 (deleted)\n'
    )
    assert observed['anonymous_executable'] == {
        'count_method': 'nonempty-permission-classes-v1',
        'count': 1, 'bytes': 4096,
        'permissions': ['r-xp'],
        'raw_vma_boundaries_recorded': False,
    }
    assert observed['openmp_deleted_semaphore']['count'] == 1
    with pytest.raises(runner.AdaptiveChildResumeError, match='deleted'):
        runner._parse_proc_maps(
            b'00001000-00002000 r-xp 00000000 00:01 3 '
            b'/tmp/evil.so (deleted)\n'
        )
    with pytest.raises(runner.AdaptiveChildResumeError, match='outside'):
        runner._mapped_path_category(Path('/opt/evil.so'))

    for key in list(os.environ):
        monkeypatch.delenv(key, raising=False)
    for key, value in runner._STRICT_ENTRY_ENVIRONMENT:
        monkeypatch.setenv(key, value)
    for key, value in runner._STRICT_DERIVED_THREAD_ENV:
        monkeypatch.setenv(key, value)
    writer_source = runner._expected_strict_derived_env_writer_record()
    derived = runner._strict_derived_environment_binding(writer_source)
    assert derived['environment'] == dict(runner._STRICT_DERIVED_THREAD_ENV)
    monkeypatch.setenv('OMP_NUM_THREADS', '2')
    with pytest.raises(runner.AdaptiveChildResumeError, match='derived'):
        runner._strict_derived_environment_binding(writer_source)
    monkeypatch.setenv('OMP_NUM_THREADS', '1')
    monkeypatch.delenv('MKL_NUM_THREADS')
    with pytest.raises(runner.AdaptiveChildResumeError, match='derived'):
        runner._strict_derived_environment_binding(writer_source)
    monkeypatch.setenv('MKL_NUM_THREADS', '1')
    monkeypatch.setenv('OMP_UNPINNED', '1')
    with pytest.raises(runner.AdaptiveChildResumeError, match='derived'):
        runner._strict_derived_environment_binding(writer_source)


def test_derived_environment_writer_requires_unique_exact_closure() -> None:
    writer = runner._expected_strict_derived_env_writer_record()

    def dummy(index: int) -> dict[str, Any]:
        return {
            'module': f'tests.synthetic_{index}',
            'path': str(PROJECT / f'tests/synthetic-{index}.py'),
            'sha256': f'{index + 1:x}' * 64,
            'bytes': index + 1,
            'externally_bound': False,
            'execution': 'compile-exact-source-bytes-v4',
        }

    tail = [dummy(0), dummy(1), dummy(2)]
    closure = [writer, *tail]
    assert runner._strict_derived_env_writer_from_executed_sources(
        closure
    ) == writer
    bad_closures = [
        tail,
        [
            {
                **writer, 'module': 'scripts.replaced_writer',
                'path': str(PROJECT / 'scripts/replaced_writer.py'),
            },
            *tail,
        ],
        [*closure, {**writer, 'module': 'scripts.duplicate_writer'}],
        [{**writer, 'sha256': '0' * 64}, *tail],
        [{**writer, 'path': str(PROJECT / 'scripts/wrong.py')}, *tail],
    ]
    for malformed in bad_closures:
        with pytest.raises(runner.AdaptiveChildResumeError, match='writer'):
            runner._strict_derived_env_writer_from_executed_sources(malformed)
    with pytest.raises(runner.AdaptiveChildResumeError, match='type-exact'):
        runner._strict_derived_env_writer_from_executed_sources([
            {**writer, 'execution': 'compile-exact-source-bytes-v3'}, *tail,
        ])
    with pytest.raises(runner.AdaptiveChildResumeError, match='exact type'):
        runner._strict_derived_env_writer_from_executed_sources(tuple(closure))


@pytest.mark.slow
@pytest.mark.skipif(
    os.environ.get('PAPER400_RUN_NFS_DMTCP_PREFLIGHT') != '1',
    reason='set PAPER400_RUN_NFS_DMTCP_PREFLIGHT=1 for /root NFS pre-cutover',
)
def test_root_nfs_dmtcp_start_checkpoint_resume_preflight() -> None:
    root = Path(os.environ['PAPER400_NFS_PREFLIGHT_ROOT'])
    assert root.is_absolute() and root.parent == Path('/root') and not root.exists()
    inputs = Path('/root') / f'.adaptive-v5-nfs-input-{os.getpid()}'
    inputs.mkdir(mode=0o700)
    cnf = inputs / 'input.cnf'
    cnf.write_bytes(b'p cnf 1 1\n1 0\n')
    solver = Path('/usr/bin/tail').resolve(strict=True)
    controller.initialize(
        root, cnf=cnf, solver=solver, dmtcp_prefix=runner.DMTCP_PREFIX,
        solver_args=['-f'], runtime_libs=runner._runtime_libraries(solver),
        runtime_libs_complete=True,
    )
    probe = root / 'nfs-probe'
    fd = os.open(probe, os.O_RDWR | os.O_CREAT | os.O_EXCL | os.O_NOFOLLOW, 0o600)
    try:
        os.write(fd, b'nfs\n'); os.fsync(fd)
        import fcntl
        fcntl.flock(fd, fcntl.LOCK_EX | fcntl.LOCK_NB)
        fcntl.flock(fd, fcntl.LOCK_UN)
    finally:
        os.close(fd)
    os.link(probe, root / 'nfs-probe.link', follow_symlinks=False)
    started = controller.start(root)
    stopped = controller.checkpoint_stop(root)
    assert controller.inspect(root, verify_hashes=True)['state'] == 'CHECKPOINTED'
    resumed = controller.resume(root)
    final = controller.checkpoint_stop(root)
    assert all(controller.selfhash_valid(item) for item in (started, stopped, resumed, final))


@pytest.mark.slow
@pytest.mark.skipif(
    os.environ.get('PAPER400_RUN_ADAPTIVE_BATCH_600S') != '1',
    reason='set PAPER400_RUN_ADAPTIVE_BATCH_600S=1 after atomic cutover',
)
def test_real_eight_root_600s_checkpoint_switch_cohort_cli() -> None:
    roots = json.loads(os.environ['PAPER400_ADAPTIVE_BATCH_ROOTS_JSON'])
    cpus = json.loads(os.environ['PAPER400_ADAPTIVE_BATCH_CPUS_JSON'])
    interpreter = Path(os.environ['PAPER400_FIXED_PYTHON_ISOLATED'])
    script = PROJECT / FINAL_RELATIVE
    def run(action: str, summary: Path) -> dict[str, Any]:
        argv = [str(interpreter), '-I', '-S', '-B', str(script), action]
        for root in roots:
            argv.extend(['--root', root])
        for cpu in cpus:
            argv.extend(['--cpu', str(cpu)])
        argv.extend(['--summary-path', str(summary)])
        result = subprocess.run(argv, stdout=subprocess.PIPE, stderr=subprocess.PIPE, check=False)
        assert result.returncode == 0, result.stderr.decode('utf-8', 'replace')
        return json.loads(result.stdout)
    deadline = time.monotonic() + 600.0
    while time.monotonic() < deadline:
        time.sleep(min(5.0, deadline - time.monotonic()))
    parent = Path(os.environ.get('PAPER400_ADAPTIVE_BATCH_SUMMARY_ROOT', '/root'))
    nonce = f'{os.getpid()}-{time.monotonic_ns()}'
    assert run('checkpoint-stop-batch', parent / f'v5-stop-{nonce}.json')['success'] is True
    target = int(os.environ.get('PAPER400_ADAPTIVE_TARGET_DESCENDANT', '1'))
    argv = [
        str(interpreter), '-I', '-S', '-B', str(script),
        'switch-cohort-batch',
    ]
    for root in roots:
        argv.extend(['--root', root])
    for cpu in cpus:
        argv.extend(['--cpu', str(cpu)])
    argv.extend([
        '--descendant-index', str(target), '--summary-path',
        str(parent / f'v5-switch-{nonce}.json'),
    ])
    switched = subprocess.run(
        argv, stdout=subprocess.PIPE, stderr=subprocess.PIPE, check=False,
    )
    assert switched.returncode == 0, switched.stderr.decode('utf-8', 'replace')
    assert json.loads(switched.stdout)['success'] is True
