from pathlib import Path

from archon.commands.qcode import _default_repo_dir, _ensure_repo


def test_default_qcode_repo_prefers_vendored_tree(tmp_path):
    vendored = tmp_path / "qcode-discovery"
    vendored.mkdir()
    (vendored / "main.py").write_text("")
    (vendored / "pyproject.toml").write_text("")
    assert _default_repo_dir(tmp_path) == vendored


def test_ensure_repo_accepts_vendored_tree_without_git(tmp_path):
    vendored = tmp_path / "qcode-discovery"
    vendored.mkdir()
    (vendored / "main.py").write_text("")
    (vendored / "pyproject.toml").write_text("")
    _ensure_repo(vendored, "https://invalid.example/repo.git")
    assert not (vendored / ".git").exists()
