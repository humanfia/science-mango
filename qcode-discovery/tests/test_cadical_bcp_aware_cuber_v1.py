import csv
import itertools
import json
import os
from pathlib import Path
import subprocess

import pytest


BINARY = os.environ.get("CADICAL_BCP_CUBER_BIN")
pytestmark = pytest.mark.skipif(
    not BINARY, reason="set CADICAL_BCP_CUBER_BIN to run native integration tests"
)


def _run(tmp_path: Path, cnf: str, target: int, candidates: int = 32):
    input_path = tmp_path / "input.cnf"
    input_path.write_text(cnf, encoding="ascii")
    prefix = tmp_path / "cover"
    completed = subprocess.run(
        [BINARY, str(input_path), str(target), str(prefix), str(candidates)],
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=False,
    )
    assert completed.returncode == 0, completed.stderr
    with (tmp_path / "cover-tree.tsv").open(newline="", encoding="ascii") as f:
        tree = list(csv.DictReader(f, delimiter="\t"))
    coverage = json.loads(
        (tmp_path / "cover-coverage.json").read_text(encoding="ascii")
    )
    cubes = []
    for line in (tmp_path / "cover.cubes").read_text(encoding="ascii").splitlines():
        fields = line.split()
        assert fields[0] == "a" and fields[-1] == "0"
        cubes.append(tuple(map(int, fields[1:-1])))
    return tree, coverage, cubes


def _matching_cube_count(cubes, assignment):
    return sum(
        all(assignment[abs(literal)] == (literal > 0) for literal in cube)
        for cube in cubes
    )


def test_bcp_fixed_chain_is_never_selected_and_balanced_variable_wins(tmp_path):
    tree, coverage, cubes = _run(
        tmp_path,
        """p cnf 6 5
1 0
-1 2 0
-2 3 0
4 5 0
-4 6 0
""",
        target=2,
    )
    root = tree[0]
    assert int(root["split_literal"]) == 4
    assert int(root["conflict_sides"]) == 0
    assert all(abs(int(row["split_literal"])) not in {1, 2, 3} for row in tree)
    assert coverage["target_reached"] is True
    assert len(cubes) == 2


def test_lookahead_unsat_is_terminal_not_numeric_fallback(tmp_path):
    tree, coverage, cubes = _run(
        tmp_path,
        """p cnf 2 4
1 2 0
1 -2 0
-1 2 0
-1 -2 0
""",
        target=4,
    )
    assert len(tree) == 1
    assert tree[0]["terminal"] == "LOOKAHEAD_UNSAT"
    assert int(tree[0]["split_literal"]) == 0
    assert coverage["observed_leaf_count"] == 1
    assert coverage["target_reached"] is False
    assert cubes == [()]


def test_safe_candidate_beats_single_conflict_candidate(tmp_path):
    tree, coverage, _ = _run(
        tmp_path,
        """p cnf 6 5
1 2 0
-1 3 0
-4 5 0
-4 -5 0
4 6 0
""",
        target=2,
    )
    root = tree[0]
    assert int(root["split_literal"]) != 4
    assert int(root["conflict_sides"]) == 0
    assert coverage["target_reached"] is True


def test_adaptive_cover_is_exactly_one_cube_for_every_assignment(tmp_path):
    _, coverage, cubes = _run(
        tmp_path,
        """p cnf 6 3
1 2 0
3 4 0
5 6 0
""",
        target=4,
    )
    assert coverage["target_reached"] is True
    assert len(cubes) == 4
    for bits in itertools.product((False, True), repeat=6):
        assignment = {index + 1: value for index, value in enumerate(bits)}
        assert _matching_cube_count(cubes, assignment) == 1
